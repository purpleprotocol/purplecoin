use criterion::*;
use mimalloc::MiMalloc;
use purplecoin::chain::ChainConfig;
use purplecoin::consensus::*;
use purplecoin::primitives::*;
use purplecoin::vm::internal::VmTerm;
use purplecoin::vm::*;
use rayon::prelude::*;
use std::collections::HashMap;

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
            let mut idx_map = HashMap::new();
            input.script.execute(
                &input.script_args,
                &[input.clone()],
                &mut out_stack,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags {
                    build_stacktrace: false,
                    validate_output_amounts: false,
                },
            )
        })
    });

    let batch_sizes = vec![100, 200, 500, 750, 1000, 1500, 2000, 2500, 3000];

    for b in batch_sizes.iter().cloned() {
        let in_clone = input.clone();
        let inputs = vec![in_clone];
        let inputs: Vec<_> = inputs.iter().cycle().take(b).collect();
        c.bench_function(&format!("verify coinbase script batch {b}"), |b| {
            b.iter(|| {
                inputs
                    .par_iter()
                    .map(|i| {
                        let mut idx_map = HashMap::new();
                        let mut out_stack = vec![];
                        i.script.execute(
                            &input.script_args,
                            &[input.clone()],
                            &mut out_stack,
                            &mut idx_map,
                            [0; 32],
                            key,
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                            },
                        )
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
            &format!("verify coinbase script batch all shards {b}"),
            |b| {
                b.iter(|| {
                    inputs
                        .par_iter()
                        .map(|i| {
                            let mut idx_map = HashMap::new();
                            let mut out_stack = vec![];
                            i.script.execute(
                                &input.script_args,
                                &[input.clone()],
                                &mut out_stack,
                                &mut idx_map,
                                [0; 32],
                                key,
                                VmFlags {
                                    build_stacktrace: false,
                                    validate_output_amounts: false,
                                },
                            )
                        })
                        .collect::<Vec<_>>()
                })
            },
        );
    }
}

fn bench_vm_abuse(c: &mut Criterion) {
    let key = "test_key";
    let ss = Script {
        version: 1,
        script: vec![
            ScriptEntry::Byte(0x03),
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Opcode(OP::Loop),
            ScriptEntry::Opcode(OP::Pick),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Opcode(OP::Pick),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Opcode(OP::Add1),
            ScriptEntry::Opcode(OP::BreakIfEq),
            ScriptEntry::Opcode(OP::End),
            ScriptEntry::Opcode(OP::Verify),
        ],
    };
    let sh = ss.to_script_hash(key);
    let args = vec![
        VmTerm::Signed128(30),
        VmTerm::Hash160([0; 20]),
        VmTerm::Hash160(sh.0),
    ];
    let ins = vec![Input {
        out: None,
        nsequence: 0xffffffff,
        colour_script_args: None,
        spending_pkey: None,
        spend_proof: None,
        witness: None,
        script: ss.clone(),
        script_args: args.clone(),
        colour_proof: None,
        colour_proof_without_address: None,
        colour_script: None,
        hash: None,
    }]
    .iter()
    .cloned()
    .map(|mut i| {
        i.compute_hash(key);
        i
    })
    .collect::<Vec<_>>();
    let batch_sizes = vec![100, 500, 1000, 1500, 2000];

    for batch_size in batch_sizes {
        c.bench_function(&format!("abuse vm {batch_size} out of gas inputs"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    assert_eq!(
                        ss.execute(
                            &args,
                            ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            [0; 32],
                            key,
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false
                            }
                        ),
                        Err((ExecutionResult::OutOfGas, StackTrace::default())).into()
                    );
                });
            })
        });
    }
}

fn bench_vm_load_var(c: &mut Criterion) {
    let key = "test_key";
    let ss = Script {
        version: 1,
        script: vec![
            ScriptEntry::Byte(0x03),
            ScriptEntry::Opcode(OP::Unsigned128Var),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x34),
            ScriptEntry::Byte(0x56),
            ScriptEntry::Byte(0x78),
            ScriptEntry::Byte(0x90),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x34),
            ScriptEntry::Byte(0x56),
            ScriptEntry::Byte(0x78),
            ScriptEntry::Byte(0x90),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x34),
            ScriptEntry::Byte(0x56),
            ScriptEntry::Byte(0x78),
            ScriptEntry::Byte(0x90),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Opcode(OP::Unsigned128Var),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x34),
            ScriptEntry::Byte(0x56),
            ScriptEntry::Byte(0x78),
            ScriptEntry::Byte(0x90),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x34),
            ScriptEntry::Byte(0x56),
            ScriptEntry::Byte(0x78),
            ScriptEntry::Byte(0x90),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x34),
            ScriptEntry::Byte(0x56),
            ScriptEntry::Byte(0x78),
            ScriptEntry::Byte(0x90),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
    };
    let script_output: Vec<VmTerm> = vec![
        VmTerm::Unsigned128(0x12907856341290785634129078563412),
        VmTerm::Unsigned128(0x12907856341290785634129078563412),
    ];
    let sh = ss.to_script_hash(key);
    let args = vec![
        VmTerm::Signed128(30),
        VmTerm::Hash160([0; 20]),
        VmTerm::Hash160(sh.0),
    ];
    let mut ins = vec![Input {
        out: None,
        nsequence: 0xffffffff,
        colour_script_args: None,
        spending_pkey: None,
        spend_proof: None,
        witness: None,
        script: ss.clone(),
        script_args: args.clone(),
        colour_proof: None,
        colour_proof_without_address: None,
        colour_script: None,
        hash: None,
    }]
    .iter()
    .cloned()
    .map(|mut i| {
        i.compute_hash(key);
        i
    })
    .collect::<Vec<_>>();

    let ins_hashes: Vec<u8> = ins.iter_mut().fold(vec![], |mut acc, v: &mut Input| {
        v.compute_hash(key);
        acc.extend(v.hash().unwrap().0);
        acc
    });
    let inputs_hash = Hash160::hash_from_slice(ins_hashes.as_slice(), key);
    let inputs_hash: Hash160 = ins.iter().cloned().cycle().take(0).fold(
        inputs_hash.clone(),
        |mut acc: Hash160, v: Input| {
            let inputs_hashes = vec![acc.0, inputs_hash.0]
                .iter()
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
            acc = Hash160::hash_from_slice(inputs_hashes.as_slice(), key);
            acc
        },
    );
    let mut oracle_out = Output {
        address: Some(Hash160::zero().to_address()),
        amount: 30,
        script_hash: sh,
        inputs_hash,
        coloured_address: None,
        coinbase_height: None,
        hash: None,
        script_outs: script_output,
        idx: 0,
    };
    oracle_out.compute_hash(key);
    let expected = vec![oracle_out];

    let batch_sizes = vec![100, 500, 1000, 1500, 2000];
    for batch_size in batch_sizes {
        c.bench_function(&format!("load u128 var, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    assert_eq!(
                        ss.execute(
                            &args,
                            ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            [0; 32],
                            key,
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, expected);
                });
            })
        });
    }
}

pub fn vm_benchmark(c: &mut Criterion) {
    bench_coinbase(c);
    bench_vm_abuse(c);
    bench_vm_load_var(c);
}

criterion_group!(benches, vm_benchmark);
criterion_main!(benches);
