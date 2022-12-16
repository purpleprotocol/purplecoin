use criterion::*;
use mimalloc::MiMalloc;
use purplecoin::chain::ChainConfig;
use purplecoin::consensus::*;
use purplecoin::primitives::*;
use purplecoin::vm::internal::VmTerm;
use purplecoin::vm::*;
use rayon::prelude::*;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn bench_coinbase(c: &mut Criterion) {
    let chain_id = 255;
    let config = ChainConfig::default();
    let address = Address::from_bech32("pu1wyzgxpzedr24l28ku8nsfwd2h4zrsqas69s3mp").unwrap();
    let key = config.get_chain_key(chain_id);
    let ss = Script::new_simple_spend();
    let sh = ss.to_script_hash(key);
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
    let mut out_stack = vec![];
    c.bench_function("verify coinbase script", |b| {
        b.iter(|| {
            input
                .script
                .execute(&input.script_args, &[input.clone()], &mut out_stack, key)
        })
    });

    let batch_sizes = vec![100, 200, 500, 750, 1000, 1500, 2000, 2500, 3000];

    for b in batch_sizes.iter().cloned() {
        let in_clone = input.clone();
        let inputs = vec![in_clone];
        let inputs: Vec<_> = inputs.iter().cycle().take(b).collect();
        c.bench_function(&format!("verify coinbase script batch {}", b), |b| {
            b.iter(|| {
                inputs
                    .par_iter()
                    .map(|i| {
                        let mut out_stack = vec![];
                        i.script
                            .execute(&input.script_args, &[input.clone()], &mut out_stack, key)
                    })
                    .collect::<Vec<_>>()
            })
        });
    }

    for b in batch_sizes {
        let in_clone = input.clone();
        let inputs = vec![in_clone];
        let inputs: Vec<_> = inputs.iter().cycle().take(b).collect();
        c.bench_function(
            &format!("verify coinbase script batch all shards {}", b),
            |b| {
                b.iter(|| {
                    inputs
                        .par_iter()
                        .map(|i| {
                            let mut out_stack = vec![];
                            i.script.execute(
                                &input.script_args,
                                &[input.clone()],
                                &mut out_stack,
                                key,
                            )
                        })
                        .collect::<Vec<_>>()
                })
            },
        );
    }
}

fn bench_vm_abuse(_c: &mut Criterion) {}

pub fn vm_benchmark(c: &mut Criterion) {
    bench_coinbase(c);
}

criterion_group!(benches, vm_benchmark);
criterion_main!(benches);
