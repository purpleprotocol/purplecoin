use bitvec::prelude::*;
use criterion::*;
use mimalloc::MiMalloc;
use purplecoin::chain::ChainConfig;
use purplecoin::consensus::*;
use purplecoin::primitives::*;
use purplecoin::vm::internal::VmTerm;
use purplecoin::vm::*;
use rayon::prelude::*;
use std::collections::HashMap;
use simdutf8::basic::from_utf8;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

const HASH_BENCH_BATCH_SIZE: [usize; 4] = [100, 500, 1000, 2000];

struct BenchBaseArgs {
    args: Vec<VmTerm>,
    ins: Vec<Input>,
    out: Vec<Output>,
}

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
        script: Script::new_coinbase(),
        input_flags: InputFlags::IsCoinbase,
        script_args,
        ..Default::default()
    };
    input.compute_hash(key);
    let mut out_stack = vec![];
    let mut sum = 0;
    c.bench_function("verify coinbase script", |b| {
        b.iter(|| {
            let mut idx_map = HashMap::new();
            let mut ver_stack = VerificationStack::new();
            assert_eq!(
                input.script.execute(
                    &input.script_args,
                    &[input.clone()],
                    &mut out_stack,
                    &mut sum,
                    &mut idx_map,
                    &mut ver_stack,
                    [0; 32],
                    key,
                    "",
                    VmFlags {
                        is_coinbase: true,
                        build_stacktrace: false,
                        validate_output_amounts: false,
                        ..Default::default()
                    },
                ),
                Ok(ExecutionResult::Ok).into()
            );
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
                        let mut sum = 0;
                        let mut ver_stack = VerificationStack::new();
                        assert_eq!(
                            i.script.execute(
                                &input.script_args,
                                &[input.clone()],
                                &mut out_stack,
                                &mut sum,
                                &mut idx_map,
                                &mut ver_stack,
                                [0; 32],
                                key,
                                "",
                                VmFlags {
                                    build_stacktrace: false,
                                    validate_output_amounts: false,
                                    is_coinbase: true,
                                    ..Default::default()
                                },
                            ),
                            Ok(ExecutionResult::Ok).into()
                        );
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
                            let mut sum = 0;
                            let mut ver_stack = VerificationStack::new();
                            assert_eq!(
                                i.script.execute(
                                    &input.script_args,
                                    &[input.clone()],
                                    &mut out_stack,
                                    &mut sum,
                                    &mut idx_map,
                                    &mut ver_stack,
                                    [0; 32],
                                    key,
                                    "",
                                    VmFlags {
                                        build_stacktrace: false,
                                        validate_output_amounts: false,
                                        is_coinbase: true,
                                        ..Default::default()
                                    },
                                ),
                                Ok(ExecutionResult::Ok).into()
                            );
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
            ScriptEntry::Opcode(OP::Ok),
        ],
        malleable_args: bitvec![0, 0, 0],
        ..Script::default()
    };
    let sh = ss.to_script_hash(key);
    let args = vec![
        VmTerm::Signed128(30),
        VmTerm::Hash160([0; 20]),
        VmTerm::Hash160(sh.0),
    ];
    let ins = vec![Input {
        script: ss.clone(),
        script_args: args.clone(),
        input_flags: InputFlags::IsCoinbase,
        ..Default::default()
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
                    let mut sum = 0;
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args,
                            ins.as_slice(),
                            &mut outs,
                            &mut sum,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                is_coinbase: true,
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Err((ExecutionResult::OutOfGas, StackTrace::default())).into()
                    );
                });
            })
        });
    }
}

fn get_bench_base_args(ss: &mut Script, out_script: Vec<VmTerm>, key: &str) -> BenchBaseArgs {
    if ss.malleable_args.is_empty() {
        if let ScriptEntry::Byte(byte) = ss.script[0] {
            let num = byte as usize;
            ss.malleable_args = (0..num).map(|_| false).collect();
        } else {
            unreachable!();
        }
    }

    let sh = ss.to_script_hash(key);
    let args = vec![
        VmTerm::Signed128(30),
        VmTerm::Hash160([0; 20]),
        VmTerm::Hash160(sh.0),
    ];

    let mut ins = vec![Input {
        script: ss.clone(),
        script_args: args.clone(),
        input_flags: InputFlags::IsCoinbase,
        ..Default::default()
    }]
        .iter()
        .cloned()
        .map(|mut i| {
            i.compute_hash(key);
            i
        })
        .collect::<Vec<_>>();

    // Prepare output
    let ins_hashes: Vec<u8> = ins.iter_mut().fold(vec![], |mut acc, v: &mut Input| {
        v.compute_hash(key);
        acc.extend(v.hash().unwrap().0);
        acc
    });
    let inputs_hash = Hash160::hash_from_slice(ins_hashes.as_slice(), key);
    let inputs_hash: Hash160 = ins.iter().cloned().cycle().take(0).fold(
        inputs_hash.clone(),
        |mut acc: Hash160, v: Input| {
            let inputs_hashes = [acc.0, inputs_hash.0]
                .iter()
                .flatten()
                .copied()
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
        script_outs: out_script,
        idx: 0,
    };
    oracle_out.compute_hash(key);

    BenchBaseArgs {
        args,
        ins,
        out: vec![oracle_out],
    }
}

fn bench_vm_load_two_u128_var(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
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
        ..Script::default()
    };
    let script_output: Vec<VmTerm> = vec![
        VmTerm::Unsigned128(0x12907856341290785634129078563412),
        VmTerm::Unsigned128(0x12907856341290785634129078563412),
    ];
    let args = get_bench_base_args(&mut ss, script_output, key);

    let batch_sizes = vec![100, 500, 1000, 1500, 2000];
    for batch_size in batch_sizes {
        c.bench_function(&format!("load u128 var, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut sum = 0;
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut sum,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}

fn bench_vm_load_u8_var(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03),
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };
    let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8(0x0a)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("load u8 var, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}

fn bench_vm_ghostrider(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
            ScriptEntry::Byte(0x20),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Byte(0x02),
            ScriptEntry::Byte(0x03),
            ScriptEntry::Byte(0x04),
            ScriptEntry::Byte(0x05),
            ScriptEntry::Byte(0x06),
            ScriptEntry::Byte(0x07),
            ScriptEntry::Byte(0x08),
            ScriptEntry::Byte(0x09),
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Byte(0x0b),
            ScriptEntry::Byte(0x0c),
            ScriptEntry::Byte(0x0d),
            ScriptEntry::Byte(0x0e),
            ScriptEntry::Byte(0x0f),
            ScriptEntry::Byte(0x10),
            ScriptEntry::Byte(0x11),
            ScriptEntry::Byte(0x12),
            ScriptEntry::Byte(0x13),
            ScriptEntry::Byte(0x14),
            ScriptEntry::Byte(0x15),
            ScriptEntry::Byte(0x16),
            ScriptEntry::Byte(0x17),
            ScriptEntry::Byte(0x18),
            ScriptEntry::Byte(0x19),
            ScriptEntry::Byte(0x1a),
            ScriptEntry::Byte(0x1b),
            ScriptEntry::Byte(0x1c),
            ScriptEntry::Byte(0x1d),
            ScriptEntry::Byte(0x1e),
            ScriptEntry::Byte(0x1f),
            ScriptEntry::Byte(0x2a),
            ScriptEntry::Opcode(OP::Unsigned8Var), // Value
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::GhostRider),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let new_key: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
        0x1d, 0x1e, 0x1f, 0x2a,
    ];

    let script_output: Vec<VmTerm> = vec![bifs::ghostrider256(&term, new_key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("ghostrider hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}

fn bench_vm_fugue256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Fugue),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::fugue256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("fugue256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_jh256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::JH256),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::jh256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("jh256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake2s256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake2s256),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake2s_256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake2s256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_sha256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Sha256),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::sha256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("sha256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_sha512(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Sha512),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::sha512(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("sha512 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_keccak256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Keccak256),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::keccak256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("keccak256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_keccak512(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Keccak512),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::keccak512(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("keccak512 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake2b256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake2b256),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake2b_256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake2b256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake2b512(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake2b512),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake2b_512(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake2b512 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_160(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_160),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_160(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_160 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_256(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_256),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_256(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_256 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_512(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_512),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_512(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_512 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_256_160(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_256_160),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_256_160(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_256_160 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_256keyed(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Byte(0x02),
            ScriptEntry::Byte(0x03),
            ScriptEntry::Byte(0x04),
            ScriptEntry::Byte(0x05),
            ScriptEntry::Byte(0x06),
            ScriptEntry::Byte(0x07),
            ScriptEntry::Byte(0x08),
            ScriptEntry::Byte(0x09),
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Opcode(OP::Unsigned8Var), // Value
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_256Keyed),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let utf_key = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a];
    let utf_key = from_utf8(utf_key.as_slice()).unwrap();
    let script_output: Vec<VmTerm> = vec![bifs::blake3_256_internal(&term, utf_key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_256keyed hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_512keyed(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Byte(0x02),
            ScriptEntry::Byte(0x03),
            ScriptEntry::Byte(0x04),
            ScriptEntry::Byte(0x05),
            ScriptEntry::Byte(0x06),
            ScriptEntry::Byte(0x07),
            ScriptEntry::Byte(0x08),
            ScriptEntry::Byte(0x09),
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Opcode(OP::Unsigned8Var), // Value
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_512Keyed),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let utf_key = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a];
    let utf_key = from_utf8(utf_key.as_slice()).unwrap();
    let script_output: Vec<VmTerm> = vec![bifs::blake3_512_internal(&term, utf_key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_512keyed hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_160keyed(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Byte(0x00),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Byte(0x02),
            ScriptEntry::Byte(0x03),
            ScriptEntry::Byte(0x04),
            ScriptEntry::Byte(0x05),
            ScriptEntry::Byte(0x06),
            ScriptEntry::Byte(0x07),
            ScriptEntry::Byte(0x08),
            ScriptEntry::Byte(0x09),
            ScriptEntry::Byte(0x0a),
            ScriptEntry::Opcode(OP::Unsigned8Var), // Value
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_160Keyed),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let utf_key = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a];
    let utf_key = from_utf8(utf_key.as_slice()).unwrap();
    let script_output: Vec<VmTerm> = vec![bifs::blake3_160_internal(&term, utf_key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_160keyed hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_160internal(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_160Internal),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_160_internal(&term, key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_160internal hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_256internal(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_256Internal),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_256_internal(&term, key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_256internal hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_512internal(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_512Internal),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_512_internal(&term, key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_512internal hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_blake3_256_160internal(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Blake3_256_160Internal),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::blake3_256_160_internal(&term, key)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("blake3_256_160internal hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}
fn bench_vm_ripemd160(c: &mut Criterion) {
    let key = "test_key";
    let mut ss = Script {
        script: vec![
            ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            ScriptEntry::Opcode(OP::Unsigned8Var),
            ScriptEntry::Byte(0x01),
            ScriptEntry::Opcode(OP::Ripemd160),
            ScriptEntry::Opcode(OP::PopToScriptOuts),
            ScriptEntry::Opcode(OP::PushOut),
            ScriptEntry::Opcode(OP::Verify),
        ],
        ..Script::default()
    };

    let term = VmTerm::Unsigned8(0x01);
    let script_output: Vec<VmTerm> = vec![bifs::ripemd160(&term)];
    let args = get_bench_base_args(&mut ss, script_output, key);

    for batch_size in HASH_BENCH_BATCH_SIZE {
        c.bench_function(&format!("ripemd160 hash, batch {batch_size}"), |b| {
            b.iter(|| {
                (0..batch_size).into_par_iter().for_each(|_| {
                    let mut outs = vec![];
                    let mut idx_map = HashMap::new();
                    let mut ver_stack = VerificationStack::new();
                    assert_eq!(
                        ss.execute(
                            &args.args,
                            args.ins.as_slice(),
                            &mut outs,
                            &mut idx_map,
                            &mut ver_stack,
                            [0; 32],
                            key,
                            "",
                            VmFlags {
                                build_stacktrace: false,
                                validate_output_amounts: false,
                                ..Default::default()
                            }
                        ),
                        Ok(ExecutionResult::OkVerify).into()
                    );
                    assert_eq!(outs, args.out);
                });
            })
        });
    }
}

pub fn vm_benchmark(c: &mut Criterion) {
    bench_coinbase(c);
    bench_vm_abuse(c);
    bench_vm_load_two_u128_var(c);
}

pub fn vm_benchmark_hash_comparison(c: &mut Criterion) {
    bench_vm_load_u8_var(c);
    bench_vm_ghostrider(c);
    bench_vm_fugue256(c);
    bench_vm_jh256(c);
    bench_vm_blake2s256(c);
    bench_vm_sha256(c);
    bench_vm_sha512(c);
    bench_vm_keccak256(c);
    bench_vm_keccak512(c);
    bench_vm_blake2b256(c);
    bench_vm_blake2b512(c);
    bench_vm_blake3_160(c);
    bench_vm_blake3_256(c);
    bench_vm_blake3_512(c);
    bench_vm_blake3_256_160(c);
    bench_vm_blake3_256keyed(c);
    bench_vm_blake3_512keyed(c);
    bench_vm_blake3_160keyed(c);
    bench_vm_blake3_160internal(c);
    bench_vm_blake3_256internal(c);
    bench_vm_blake3_512internal(c);
    bench_vm_blake3_256_160internal(c);
    bench_vm_ripemd160(c);
}

// criterion_group!(benches, vm_benchmark);
criterion_group!(benches_hash, vm_benchmark_hash_comparison);
// criterion_main!(benches);
criterion_main!(benches_hash);
