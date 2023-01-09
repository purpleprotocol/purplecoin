use accumulator::group::Rsa2048;
use accumulator::Accumulator;
use accumulator::Witness;
use criterion::*;
use mimalloc::MiMalloc;
use purplecoin::chain::ChainConfig;
use purplecoin::consensus::*;
use purplecoin::primitives::*;
use purplecoin::vm::internal::VmTerm;
use purplecoin::vm::*;
use rand::prelude::*;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn transaction_batch_benchmark(c: &mut Criterion) {
    let batch_sizes = vec![250, 500, 750, 1000, 1500, 2000, 2500, 3500, 4000];
    let chain_id = 255;
    let config = ChainConfig::default();
    let address = Address::from_bech32("pu1wyzgxpzedr24l28ku8nsfwd2h4zrsqas69s3mp").unwrap();
    let key = config.get_chain_key(chain_id);
    let ss = Script::new_simple_spend();
    let sh = ss.to_script_hash(key);
    let mut out_stack = vec![];
    let mut idx_map = HashMap::new();
    let script_args = vec![
        VmTerm::Signed128(INITIAL_BLOCK_REWARD),
        VmTerm::Hash160(address.0),
        VmTerm::Hash160(sh.0),
        VmTerm::Unsigned64(1),
        VmTerm::Unsigned32(0),
    ];
    let mut input = Input {
        out: None,
        witness: None,
        spend_proof: None,
        colour_proof: None,
        colour_proof_without_address: None,
        spending_pkey: None,
        colour_script: None,
        colour_script_args: None,
        script: Script::new_coinbase(),
        script_args,
        nsequence: 0xffffffff,
        hash: None,
    };
    input.compute_hash(key);

    let mut group = c.benchmark_group("accumulator");
    group.sample_size(10);

    for batch_size in batch_sizes.iter() {
        let in_clone = input.clone();
        input.script.execute(
            &input.script_args,
            &[in_clone],
            &mut out_stack,
            &mut idx_map,
            [0; 32],
            key,
        );

        let outputs: Vec<Output> = out_stack
            .iter()
            .cycle()
            .take(*batch_size * SHARDS_PER_SECTOR)
            .cloned()
            .map(|mut o| {
                o.inputs_hash = Hash160(rand::thread_rng().gen());
                o.hash = None;
                o.compute_hash(key);
                o
            })
            .collect();

        let mut witness_all = Witness(Accumulator::<Rsa2048, Hash256>::empty());
        let mut next_to_delete = vec![];
        let mut outs_vec = vec![];

        let accumulators_with_proofs: Vec<_> = outputs
            .chunks(SHARDS_PER_SECTOR * ACCUMULATOR_MULTIPLIER)
            .map(|outs| {
                let out_hashes: Vec<_> = outs.iter().map(|o| *o.hash().unwrap()).collect();
                let accumulator1 = Accumulator::<Rsa2048, Hash256>::empty();
                let (witness_deleted, _proof_deleted) =
                    accumulator1.delete_with_proof(&[]).unwrap();
                let (accumulator2, proof_added) = witness_deleted.add_with_proof(&out_hashes);

                (accumulator2, proof_added, out_hashes)
            })
            .collect();

        group.bench_function(
            &format!(
                "verify membership batch all shards in a single sector 100% cache hit rate {batch_size}"
            ),
            |b| {
                b.iter(|| {
                    accumulators_with_proofs
                        .par_iter()
                        .map(|(accumulator, proof_added, out_hashes)| {
                            accumulator.verify_membership_batch(out_hashes, proof_added)
                        })
                        .collect::<Vec<_>>();
                });
            },
        );

        accumulator::hash::clear_cache_percentage(0.95);

        group.bench_function(
            &format!(
                "verify membership batch all shards in a single sector 95% cache hit rate {batch_size}"
            ),
            |b| {
                b.iter(|| {
                    accumulators_with_proofs
                        .par_iter()
                        .map(|(accumulator, proof_added, out_hashes)| {
                            accumulator.verify_membership_batch(out_hashes, proof_added)
                        })
                        .collect::<Vec<_>>();
                    accumulator::hash::clear_cache_percentage(0.95);
                });
            },
        );

        accumulator::hash::clear_cache();

        group.bench_function(
            &format!("verify membership batch all shards in a single sector uncached {batch_size}"),
            |b| {
                b.iter(|| {
                    accumulators_with_proofs
                        .par_iter()
                        .map(|(accumulator, proof_added, out_hashes)| {
                            accumulator.verify_membership_batch(out_hashes, proof_added)
                        })
                        .collect::<Vec<_>>();
                    accumulator::hash::clear_cache();
                })
            },
        );

        let out_hashes: Vec<_> = outputs.iter().map(|o| *o.hash().unwrap()).collect();
        let (witness_deleted, _pd) = Accumulator::<Rsa2048, Hash256>::empty()
            .delete_with_proof(&next_to_delete)
            .unwrap();
        let (accumulator2, pa) = witness_deleted.add_with_proof(&out_hashes);
        let witnesses = pa.witness.compute_individual_witnesses(&out_hashes);
        let deleted_set: HashSet<_> = next_to_delete.iter().map(|(o, _)| *o).collect();
        let _deleted: Vec<_> = next_to_delete.iter().map(|(o, _)| *o).collect();
        outs_vec.retain(|(o, _)| !deleted_set.contains(o));
        outs_vec.extend(witnesses);
        let outs: Vec<_> = outs_vec.iter().map(|(o, _)| *o).collect();
        witness_all = accumulator2
            .clone()
            .update_membership_witness(witness_all.clone(), &outs, &[], &[])
            .unwrap();

        //outs_vec = witness_all.clone().compute_individual_witnesses(&outs);

        witness_all = accumulator2
            .clone()
            .update_membership_witness(witness_all.clone(), &outs, &[], &[])
            .unwrap();

        let outputs: Vec<Output> = out_stack
            .iter()
            .cycle()
            .take(*batch_size / ACCUMULATOR_MULTIPLIER) // Maintain output number
            .cloned()
            .map(|mut o| {
                o.inputs_hash = Hash160(rand::thread_rng().gen());
                o.hash = None;
                o.compute_hash(key);
                o
            })
            .collect();

        outs_vec = witness_all.clone().compute_individual_witnesses(&outs);
        outs_vec.shuffle(&mut rand::thread_rng());
        next_to_delete = outs_vec
            .iter()
            .take(*batch_size / ACCUMULATOR_MULTIPLIER)
            .cloned()
            .collect();
        let accumulator = accumulator2;
        let out_hashes: Vec<_> = outputs.iter().map(|o| *o.hash().unwrap()).collect();

        // Warmup the cache
        let (witness_deleted, _pd) = accumulator
            .clone()
            .delete_with_proof(&next_to_delete)
            .unwrap();
        let (_accumulator2, _pa) = witness_deleted.add_with_proof(&out_hashes);

        group.bench_function(
            &format!("mutate accumulators for all shards in sector 100% cache hit rate {batch_size} half added and half deleted"),
            |b| {
                b.iter(|| {
                    (0..(SHARDS_PER_SECTOR*ACCUMULATOR_MULTIPLIER))
                        .into_par_iter()
                        .for_each(|_|  {
                            let (witness_deleted, _pd) = accumulator.clone().delete_with_proof(&next_to_delete).unwrap();
                            let (_accumulator2, _pa) = witness_deleted.add_with_proof(&out_hashes);
                        });
                });
            },
        );
    }
}

criterion_group!(benches, transaction_batch_benchmark);
criterion_main!(benches);
