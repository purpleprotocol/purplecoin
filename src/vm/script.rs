// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::SCRIPT_LIMIT_OPCODES;
use crate::primitives::{Address, Hash160, Input, Output};
use crate::vm::internal::VmTerm;
use crate::vm::opcodes::OP;
use bincode::{Decode, Encode};
use ibig::{ibig, ubig};
use num_traits::{FromPrimitive, ToPrimitive};
use rand::prelude::*;
use rand_pcg::Pcg64;
use rand_seeder::Seeder;
use std::collections::HashMap;
use std::mem;

use super::bifs;

/// Max frame stack size
pub const MAX_FRAMES: usize = 512;

/// Max stack size
pub const STACK_SIZE: usize = 256;

/// VM max memory size in bytes
pub const MEMORY_SIZE: usize = 512_000;

/// Max output stack size
pub const MAX_OUT_STACK: usize = 300;

/// Return only the last n frames or top stack frame items
pub const TRACE_SIZE: usize = 10;

macro_rules! check_top_stack_val {
    ($exp:expr, $frame:expr, $frame_stack:expr, $structt:expr, $flags:expr) => {
        if $exp == &1 {
            return Ok(ExecutionResult::Ok).into();
        } else {
            let mut stack_trace = StackTrace::default();

            if $flags.build_stacktrace {
                stack_trace.trace.push(
                    (
                        $frame.i_ptr,
                        $frame.func_idx,
                        $structt.script[$frame.i_ptr].clone(),
                    )
                        .into(),
                );
                stack_trace.top_frame_stack.extend_from_slice(&$frame.stack);
                stack_trace.extend_from_frame_stack(&$frame_stack, &$structt);
            }

            return Err((ExecutionResult::Invalid, stack_trace)).into();
        }
    };
}

macro_rules! var_load {
    ($frame:expr, $script:expr, $sum:ident, $type:ty, $step:expr) => {
        $frame.i_ptr += 1;
        if let ScriptEntry::Byte(byte) = $script.script[$frame.i_ptr] {
            $sum += (byte as $type);
        } else {
            unreachable!()
        }
    };

    ($frame:expr, $script:expr, $sum:ident, $type:ty, $step:expr, $($tail:expr), +) => {
        var_load!($frame, $script, $sum, $type, $($tail), +);

        $frame.i_ptr += 1;
        if let ScriptEntry::Byte(byte) = $script.script[$frame.i_ptr] {
            $sum += (byte as $type) << $step;
        } else {
            unreachable!()
        }
    };
}

#[derive(PartialEq, Debug, Clone)]
pub enum ScriptEntry {
    Opcode(OP),
    Byte(u8),
}

#[derive(Debug, Clone)]
pub struct Frame<'a> {
    pub stack: Vec<VmTerm>,
    pub i_ptr: usize,
    pub func_idx: usize,
    pub is_loop: Option<(usize, usize)>,
    pub executor: ScriptExecutor<'a>,
}

impl<'a> Frame<'a> {
    pub fn new(func_idx: usize) -> Self {
        Self {
            stack: Vec::with_capacity(STACK_SIZE),
            i_ptr: 0,
            func_idx,
            executor: ScriptExecutor::new(),
            is_loop: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct VmFlags {
    /// Whether or not to build a stacktrace
    pub build_stacktrace: bool,

    /// Wheter or not to validate output amounts based on inputs
    pub validate_output_amounts: bool,
}

impl Default for VmFlags {
    fn default() -> Self {
        Self {
            build_stacktrace: true,
            validate_output_amounts: false,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Script {
    pub version: u8,
    pub script: Vec<ScriptEntry>,
}

impl Script {
    pub fn new_coinbase() -> Script {
        Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x05), // 5 arguments are pushed onto the stack: out_amount, out_address, out_script_hash, coinbase_height, extra_nonce
                ScriptEntry::Opcode(OP::PushCoinbaseOut),
            ],
        }
    }

    pub fn new_coinbase_without_spending_address() -> Script {
        Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x04), // 4 arguments are pushed onto the stack: out_amount, out_script_hash, coinbase_height, extra_nonce
                ScriptEntry::Opcode(OP::PushCoinbaseOutNoSpendAddress),
            ],
        }
    }

    pub fn new_simple_spend() -> Script {
        Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOutVerify),
            ],
        }
    }

    pub fn execute(
        &self,
        args: &[VmTerm],
        input_stack: &[Input],
        output_stack: &mut Vec<Output>,
        output_stack_idx_map: &mut HashMap<(Address, Hash160), u16>,
        seed: [u8; 32],
        key: &str,
        flags: VmFlags,
    ) -> VmResult {
        if self.version > 1 {
            return Ok(ExecutionResult::Ok).into();
        }

        if args.len() > STACK_SIZE {
            return Err((
                ExecutionResult::TooManyArgs,
                StackTrace {
                    trace: vec![(0_usize, 0_usize, self.script[0].clone()).into()],
                    top_frame_stack: vec![],
                },
            ))
            .into();
        }

        if self.version == 0 {
            return Err((
                ExecutionResult::BadVersion,
                StackTrace {
                    trace: vec![(0_usize, 0_usize, self.script[0].clone()).into()],
                    top_frame_stack: vec![],
                },
            ))
            .into();
        }

        let funcs = match self.parse_funcs() {
            Ok(funcs) => funcs,
            Err(r) => {
                return Err((
                    r,
                    StackTrace {
                        trace: vec![(0_usize, 0_usize, self.script[0].clone()).into()],
                        top_frame_stack: vec![],
                    },
                ))
                .into()
            }
        };

        // Seed RNG
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        // Initialize internals
        let mut memory_size = 0;
        let mut exec_count = 0;
        let mut frame_stack: Vec<Frame> = Vec::with_capacity(MAX_FRAMES);
        let mut frame = Frame::new(0);
        let mut script_outputs = vec![];

        for a in args.iter().rev().cloned() {
            memory_size += a.size();
            frame.stack.push(a);
        }
        frame_stack.push(frame);

        let inputs_hashes = input_stack
            .iter()
            .fold(vec![], |mut acc: Vec<u8>, i: &Input| {
                acc.extend_from_slice(i.hash().unwrap().as_bytes());
                acc
            });
        let inputs_hash = Hash160::hash_from_slice(&inputs_hashes, key);

        loop {
            let mut new_frame = None;
            let mut pop_frame = false;
            let mut set_ip = None;
            let fs_len = frame_stack.len();

            if let Some(frame) = frame_stack.last_mut() {
                let f = &funcs[frame.func_idx];

                if frame.i_ptr >= f.script.len() {
                    pop_frame = true
                } else {
                    let i = &f.script[frame.i_ptr];

                    // Execute opcode
                    frame.executor.push_op(
                        i,
                        frame.i_ptr,
                        frame.func_idx,
                        &inputs_hash,
                        &mut memory_size,
                        &mut frame.stack,
                        input_stack,
                        output_stack,
                        output_stack_idx_map,
                        &mut script_outputs,
                        key,
                    );
                    exec_count += 1;

                    // Check for new frames or if we should pop one
                    match &frame.executor.state {
                        ScriptExecutorState::NewLoopFrame => {
                            let mut nf = frame.clone();

                            nf.i_ptr += 1;

                            let start_i = nf.i_ptr;
                            let mut end_i = nf.i_ptr + 1;

                            // Find end instruction idx
                            loop {
                                if let ScriptEntry::Opcode(OP::End) = self.script[end_i] {
                                    break;
                                }

                                end_i += 1;
                            }

                            nf.is_loop = Some((start_i, end_i));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            nf.executor.state = ScriptExecutorState::ExpectingInitialOP;

                            for t in nf.stack.iter() {
                                memory_size += t.size();
                            }

                            new_frame = Some(nf);
                        }

                        ScriptExecutorState::BreakLoop => {
                            if let Some((_, end_i)) = frame.is_loop {
                                set_ip = Some(end_i);
                                pop_frame = true;
                            } else {
                                unreachable!()
                            }
                        }

                        ScriptExecutorState::ContinueLoop => {
                            if let Some((start_i, _)) = frame.is_loop {
                                frame.i_ptr = start_i;
                                frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            } else {
                                unreachable!()
                            }
                        }

                        ScriptExecutorState::EndBlock => {
                            if let Some((start_i, _)) = frame.is_loop {
                                frame.i_ptr = start_i;
                                frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            } else {
                                pop_frame = true;
                            }
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomHash160Var) => {
                            frame.stack.push(VmTerm::Hash160(rng.gen::<[u8; 20]>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 20;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomHash256Var) => {
                            frame.stack.push(VmTerm::Hash256(rng.gen::<[u8; 32]>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 32;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomHash512Var) => {
                            let mut res = [0; 64];

                            res[..32].copy_from_slice(&rng.gen::<[u8; 32]>());
                            res[32..64].copy_from_slice(&rng.gen::<[u8; 32]>());

                            frame.stack.push(VmTerm::Hash512(res));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 64;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned8Var) => {
                            frame.stack.push(VmTerm::Unsigned8(rng.gen::<u8>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 1;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned16Var) => {
                            frame.stack.push(VmTerm::Unsigned16(rng.gen::<u16>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 2;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned32Var) => {
                            frame.stack.push(VmTerm::Unsigned32(rng.gen::<u32>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 4;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned64Var) => {
                            frame.stack.push(VmTerm::Unsigned64(rng.gen::<u64>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 8;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned128Var) => {
                            frame.stack.push(VmTerm::Unsigned128(rng.gen::<u128>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 16;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned8Var) => {
                            frame.stack.push(VmTerm::Signed8(rng.gen::<i8>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 1;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned16Var) => {
                            frame.stack.push(VmTerm::Signed16(rng.gen::<i16>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 2;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned32Var) => {
                            frame.stack.push(VmTerm::Signed32(rng.gen::<i32>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 4;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned64Var) => {
                            frame.stack.push(VmTerm::Signed64(rng.gen::<i64>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 8;
                        }

                        ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned128Var) => {
                            frame.stack.push(VmTerm::Signed128(rng.gen::<i128>()));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 16;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash160Var) => {
                            let mut arr: [u8; 20] = [0; 20];

                            for i in 0..20 {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                    arr[i] = *byte;
                                } else {
                                    unreachable!()
                                }
                            }

                            frame.stack.push(VmTerm::Hash160(arr));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 20;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash256Var) => {
                            let mut arr: [u8; 32] = [0; 32];

                            for i in 0..32 {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                    arr[i] = *byte;
                                } else {
                                    unreachable!()
                                }
                            }

                            frame.stack.push(VmTerm::Hash256(arr));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 32;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash512Var) => {
                            let mut arr: [u8; 64] = [0; 64];

                            for i in 0..64 {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                    arr[i] = *byte;
                                } else {
                                    unreachable!()
                                }
                            }

                            frame.stack.push(VmTerm::Hash512(arr));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 64;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8Var) => {
                            frame.i_ptr += 1;

                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                frame.stack.push(VmTerm::Unsigned8(*byte));
                                frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                                frame.i_ptr += 1;
                                memory_size += 1;
                            } else {
                                unreachable!()
                            }
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned16Var) => {
                            let mut sum: u16 = 0;

                            var_load!(frame, f, sum, u16, 8, 0);

                            frame.stack.push(VmTerm::Unsigned16(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 2;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned32Var) => {
                            let mut sum: u32 = 0;

                            var_load!(frame, f, sum, u32, 24, 16, 8, 0);

                            frame.stack.push(VmTerm::Unsigned32(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 4;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned64Var) => {
                            let mut sum: u64 = 0;

                            var_load!(frame, f, sum, u64, 56, 48, 40, 32, 24, 16, 8, 0);

                            frame.stack.push(VmTerm::Unsigned64(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 8;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned128Var) => {
                            let mut sum: u128 = 0;

                            var_load!(
                                frame, f, sum, u128, 120, 112, 104, 96, 88, 80, 72, 64, 56, 48, 40,
                                32, 24, 16, 8, 0
                            );

                            frame.stack.push(VmTerm::Unsigned128(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 16;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed8Var) => {
                            frame.i_ptr += 1;

                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                let byte = unsafe { mem::transmute::<u8, i8>(*byte) };
                                frame.stack.push(VmTerm::Signed8(byte));
                                frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                                frame.i_ptr += 1;
                                memory_size += 1;
                            } else {
                                unreachable!()
                            }
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed16Var) => {
                            let mut sum: u16 = 0;

                            var_load!(frame, f, sum, u16, 8, 0);

                            let sum = unsafe { mem::transmute::<u16, i16>(sum) };
                            frame.stack.push(VmTerm::Signed16(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 2;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed32Var) => {
                            let mut sum: u32 = 0;

                            var_load!(frame, f, sum, u32, 24, 16, 8, 0);

                            let sum = unsafe { mem::transmute::<u32, i32>(sum) };
                            frame.stack.push(VmTerm::Signed32(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 4;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed64Var) => {
                            let mut sum: u64 = 0;

                            var_load!(frame, f, sum, u64, 56, 48, 40, 32, 24, 16, 8, 0);

                            let sum = unsafe { mem::transmute::<u64, i64>(sum) };
                            frame.stack.push(VmTerm::Signed64(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 8;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed128Var) => {
                            let mut sum: u128 = 0;

                            var_load!(
                                frame, f, sum, u128, 120, 112, 104, 96, 88, 80, 72, 64, 56, 48, 40,
                                32, 24, 16, 8, 0
                            );

                            let sum = unsafe { mem::transmute::<u128, i128>(sum) };
                            frame.stack.push(VmTerm::Signed128(sum));
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                            memory_size += 16;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<u8> = Vec::new();
                            for _ in 0..len {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                    arr.push(*byte);
                                } else {
                                    unreachable!()
                                }
                            }

                            let term = VmTerm::Unsigned8Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned16ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<u16> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u16 = 0;

                                var_load!(frame, f, sum, u16, 8, 0);

                                arr.push(sum);
                            }

                            let term = VmTerm::Unsigned16Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned32ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<u32> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u32 = 0;

                                var_load!(frame, f, sum, u32, 24, 16, 8, 0);

                                arr.push(sum);
                            }

                            let term = VmTerm::Unsigned32Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned64ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<u64> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u64 = 0;

                                var_load!(frame, f, sum, u64, 56, 48, 40, 32, 24, 16, 8, 0);

                                arr.push(sum);
                            }

                            let term = VmTerm::Unsigned64Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(
                            OP::Unsigned128ArrayVar,
                        ) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<u128> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u128 = 0;

                                var_load!(
                                    frame, f, sum, u128, 120, 112, 104, 96, 88, 80, 72, 64, 56, 48,
                                    40, 32, 24, 16, 8, 0
                                );

                                arr.push(sum);
                            }

                            let term = VmTerm::Unsigned128Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed8ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<i8> = Vec::new();
                            for _ in 0..len {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                    let byte = unsafe { mem::transmute::<u8, i8>(*byte) };
                                    arr.push(byte);
                                } else {
                                    unreachable!()
                                }
                            }

                            let term = VmTerm::Signed8Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed16ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<i16> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u16 = 0;

                                var_load!(frame, f, sum, u16, 8, 0);

                                let sum = unsafe { mem::transmute::<u16, i16>(sum) };
                                arr.push(sum);
                            }

                            let term = VmTerm::Signed16Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed32ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<i32> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u32 = 0;

                                var_load!(frame, f, sum, u32, 24, 16, 8, 0);

                                let sum = unsafe { mem::transmute::<u32, i32>(sum) };
                                arr.push(sum);
                            }

                            let term = VmTerm::Signed32Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed64ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<i64> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u64 = 0;

                                var_load!(frame, f, sum, u64, 56, 48, 40, 32, 24, 16, 8, 0);

                                let sum = unsafe { mem::transmute::<u64, i64>(sum) };
                                arr.push(sum);
                            }

                            let term = VmTerm::Signed64Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed128ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += *byte as u16;
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f.script[frame.i_ptr] {
                                len += (*byte as u16) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<i128> = Vec::new();
                            for _ in 0..len {
                                let mut sum: u128 = 0;

                                var_load!(
                                    frame, f, sum, u128, 120, 112, 104, 96, 88, 80, 72, 64, 56, 48,
                                    40, 32, 24, 16, 8, 0
                                );

                                let sum = unsafe { mem::transmute::<u128, i128>(sum) };
                                arr.push(sum);
                            }

                            let term = VmTerm::Signed128Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        // Extend stack trace
                        ScriptExecutorState::Error(err, stack_trace) => {
                            let mut stack_trace = stack_trace.clone();
                            frame.executor.state = ScriptExecutorState::Error(*err, stack_trace);
                        }

                        _ => {
                            frame.i_ptr += 1;
                        }
                    }
                }
            } else {
                unreachable!();
            }

            // Check if we are done
            match frame_stack.last().unwrap().executor.done() {
                None => {}
                Some(result) => match result {
                    Ok(res) => return Ok(res).into(),
                    Err((result, mut stack_trace)) => {
                        let fs_len = frame_stack.len();

                        if flags.build_stacktrace {
                            stack_trace.extend_from_frame_stack(&frame_stack[..fs_len - 1], self);
                        }

                        return Err((result, stack_trace)).into();
                    }
                },
            }

            if exec_count > SCRIPT_LIMIT_OPCODES {
                let mut stack_trace = StackTrace::default();
                let i_ptr = frame_stack.last().unwrap().i_ptr;
                let fs_len = frame_stack.len();

                if flags.build_stacktrace {
                    stack_trace.trace.push(
                        (
                            i_ptr,
                            frame_stack.last().unwrap().func_idx,
                            self.script[i_ptr].clone(),
                        )
                            .into(),
                    );
                    stack_trace.extend_from_frame_stack(&frame_stack[..fs_len - 1], self);
                }
                return Err((ExecutionResult::OutOfGas, stack_trace)).into();
            }

            if memory_size > MEMORY_SIZE {
                let mut stack_trace = StackTrace::default();
                let i_ptr = frame_stack.last().unwrap().i_ptr;
                let fs_len = frame_stack.len();

                if flags.build_stacktrace {
                    stack_trace.trace.push(
                        (
                            i_ptr,
                            frame_stack.last().unwrap().func_idx,
                            self.script[i_ptr].clone(),
                        )
                            .into(),
                    );
                    stack_trace.extend_from_frame_stack(&frame_stack[..fs_len - 1], self);
                }

                return Err((ExecutionResult::OutOfMemory, stack_trace)).into();
            }

            if pop_frame {
                let frame = frame_stack.pop().unwrap();
                let fs_len = frame_stack.len();

                // Check the top of the stack for the execution result
                if fs_len == 0 {
                    if frame.stack.is_empty() {
                        let mut stack_trace = StackTrace::default();
                        if flags.build_stacktrace {
                            stack_trace.trace.push(
                                (
                                    frame.i_ptr - 1,
                                    frame.func_idx,
                                    self.script[frame.i_ptr - 1].clone(),
                                )
                                    .into(),
                            );
                        }
                        return Err((ExecutionResult::Invalid, stack_trace)).into();
                    }

                    let top = &frame.stack[0];

                    match top {
                        VmTerm::Signed8(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags)
                        }
                        VmTerm::Signed16(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags)
                        }
                        VmTerm::Signed32(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags)
                        }
                        VmTerm::Signed64(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags)
                        }
                        VmTerm::Signed128(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags)
                        }
                        VmTerm::SignedBig(v) => {
                            if v == &ibig!(1) {
                                return Ok(ExecutionResult::Ok).into();
                            } else {
                                let mut stack_trace = StackTrace::default();

                                if flags.build_stacktrace {
                                    stack_trace.trace.push(
                                        (
                                            frame.i_ptr - 1,
                                            frame.func_idx,
                                            self.script[frame.i_ptr - 1].clone(),
                                        )
                                            .into(),
                                    );
                                    stack_trace.top_frame_stack.extend_from_slice(&frame.stack);
                                    stack_trace.extend_from_frame_stack(&frame_stack, self);
                                }

                                return Err((ExecutionResult::Invalid, stack_trace)).into();
                            }
                        }
                        _ => {
                            let mut stack_trace = StackTrace::default();

                            if flags.build_stacktrace {
                                stack_trace.trace.push(
                                    (
                                        frame.i_ptr - 1,
                                        frame.func_idx,
                                        self.script[frame.i_ptr - 1].clone(),
                                    )
                                        .into(),
                                );
                                stack_trace.extend_from_frame_stack(&frame_stack, self);
                            }

                            return Err((ExecutionResult::Invalid, stack_trace)).into();
                        }
                    }
                } else {
                    let mut parent_frame = &mut frame_stack[fs_len - 1];
                    let mut parent_stack = &mut parent_frame.stack;

                    if let Some(ip) = set_ip {
                        parent_frame.i_ptr = ip;
                        parent_frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                        set_ip = None;
                    }

                    parent_frame.i_ptr += 1;

                    // Push terms on the parent stack
                    for t in frame.stack.iter().rev().cloned() {
                        parent_stack.push(t);

                        if parent_stack.len() > STACK_SIZE {
                            let mut stack_trace = StackTrace::default();

                            if flags.build_stacktrace {
                                stack_trace.trace.push(
                                    (
                                        frame.i_ptr - 1,
                                        frame.func_idx,
                                        self.script[frame.i_ptr - 1].clone(),
                                    )
                                        .into(),
                                );
                                stack_trace.extend_from_frame_stack(&frame_stack, self);
                            }
                            return Err((ExecutionResult::StackOverflow, stack_trace)).into();
                        }
                    }
                }
            }

            if let Some(new_frame) = new_frame {
                if frame_stack.len() > MAX_FRAMES {
                    let frame = frame_stack.last().unwrap();
                    let mut stack_trace = StackTrace::default();
                    if flags.build_stacktrace {
                        stack_trace.trace.push(
                            (
                                frame.i_ptr,
                                frame.func_idx,
                                self.script[new_frame.i_ptr].clone(),
                            )
                                .into(),
                        );
                        stack_trace.extend_from_frame_stack(&frame_stack, self);
                    }
                    return Err((ExecutionResult::StackOverflow, stack_trace)).into();
                }

                frame_stack.push(new_frame);
            }
        }
    }

    pub fn to_script_hash(&self, key: &str) -> Hash160 {
        Hash160::hash_from_slice(crate::codec::encode_to_vec(&self).unwrap(), key)
    }

    #[inline]
    pub fn parse_funcs(&self) -> Result<Vec<Script>, ExecutionResult> {
        let mut out = vec![];

        match self.script[0] {
            ScriptEntry::Opcode(OP::Func) => {
                unimplemented!()
            }

            ScriptEntry::Byte(args_len) if args_len > 0 => {
                let mut out_script = Script {
                    version: 1,
                    script: vec![],
                };

                for op in self.script.iter() {
                    out_script.script.push(op.clone());
                }

                out.push(out_script);
            }

            _ => return Err(ExecutionResult::BadFormat),
        }

        Ok(out)
    }
}

#[derive(Debug, Clone)]
pub struct ScriptExecutor<'a> {
    state: ScriptExecutorState<'a>,
}

impl<'a> ScriptExecutor<'a> {
    pub fn new() -> Self {
        Self {
            state: ScriptExecutorState::ExpectingArgsLen,
        }
    }

    #[inline]
    pub fn push_op(
        &mut self,
        op: &ScriptEntry,
        i_ptr: usize,
        func_idx: usize,
        inputs_hash: &Hash160,
        memory_size: &mut usize,
        exec_stack: &mut Vec<VmTerm>,
        input_stack: &[Input],
        output_stack: &mut Vec<Output>,
        output_stack_idx_map: &mut HashMap<(Address, Hash160), u16>,
        script_outputs: &mut Vec<VmTerm>,
        key: &str,
    ) {
        match self.state {
            ScriptExecutorState::ExpectingArgsLen => match op {
                ScriptEntry::Byte(args_len) => {
                    let args_len = *args_len as usize;
                    if exec_stack.len() != args_len {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                _ => {
                    self.state = ScriptExecutorState::Error(
                        ExecutionResult::BadFormat,
                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                    );
                }
            },

            ScriptExecutorState::ExpectingIndexU8(last_op) => match (last_op, op) {
                (OP::Pick, ScriptEntry::Byte(idx)) => {
                    if *idx as usize >= exec_stack.len() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::IndexOutOfBounds,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let cloned = exec_stack[exec_stack.len() - 1 - *idx as usize].clone();
                    *memory_size += cloned.size();
                    exec_stack.push(cloned);

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                (OP::Roll, ScriptEntry::Byte(idx)) => {
                    if *idx as usize >= exec_stack.len() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::IndexOutOfBounds,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let rolled = exec_stack.remove(exec_stack.len() - 1 - *idx as usize);
                    exec_stack.push(rolled);

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                (OP::PickToScriptOuts, ScriptEntry::Byte(idx)) => {
                    if *idx as usize >= exec_stack.len() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::IndexOutOfBounds,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let cloned = exec_stack[exec_stack.len() - 1 - *idx as usize].clone();
                    script_outputs.push(cloned);

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                _ => {
                    self.state = ScriptExecutorState::Error(
                        ExecutionResult::BadFormat,
                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                    );
                }
            },

            ScriptExecutorState::ExpectingInitialOP => match op {
                ScriptEntry::Byte(_) => {
                    self.state = ScriptExecutorState::Error(
                        ExecutionResult::BadFormat,
                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                    );
                }

                ScriptEntry::Opcode(OP::PushOut) => {
                    if exec_stack.len() < 3 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let amount = exec_stack.pop().unwrap();
                    *memory_size -= amount.size();
                    let address = exec_stack.pop().unwrap();
                    *memory_size -= address.size();
                    let script_hash = exec_stack.pop().unwrap();
                    *memory_size -= script_hash.size();

                    match (amount, address, script_hash) {
                        (
                            VmTerm::Signed128(amount),
                            VmTerm::Hash160(addr),
                            VmTerm::Hash160(script_hash),
                        ) if amount > 0 => {
                            let address = Address(addr);
                            let script_hash = Hash160(script_hash);

                            if let Some(idx) =
                                output_stack_idx_map.get(&(address.clone(), script_hash.clone()))
                            {
                                // Re-hash inputs
                                let inputs_hashes: Vec<u8> = vec![
                                    output_stack[*idx as usize].inputs_hash.clone(),
                                    inputs_hash.clone(),
                                ]
                                .iter()
                                .fold(vec![], |mut acc, hash| {
                                    acc.extend(hash.0);
                                    acc
                                });

                                let inputs_hash = Hash160::hash_from_slice(inputs_hashes, key);

                                output_stack[*idx as usize].amount += amount;
                                output_stack[*idx as usize].inputs_hash = inputs_hash;
                                output_stack[*idx as usize].compute_hash(key);
                                output_stack[*idx as usize].script_outs = script_outputs.clone();

                                *script_outputs = vec![];
                            } else {
                                let mut output = Output {
                                    amount,
                                    address: Some(address.clone()),
                                    script_hash: script_hash.clone(),
                                    coinbase_height: None,
                                    coloured_address: None,
                                    inputs_hash: inputs_hash.clone(),
                                    idx: output_stack.len() as u16,
                                    script_outs: script_outputs.clone(),
                                    hash: None,
                                };

                                output.compute_hash(key);
                                output_stack_idx_map
                                    .insert((address, script_hash), output_stack.len() as u16);
                                output_stack.push(output);
                                *script_outputs = vec![];
                            }

                            if output_stack.len() > MAX_OUT_STACK {
                                self.state = ScriptExecutorState::Error(
                                    ExecutionResult::OutStackOverflow,
                                    (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                                );
                                return;
                            }

                            self.state = ScriptExecutorState::ExpectingInitialOP;
                        }

                        _ => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::PushOutVerify) => {
                    if exec_stack.len() < 3 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let amount = exec_stack.pop().unwrap();
                    let address = exec_stack.pop().unwrap();
                    let script_hash = exec_stack.pop().unwrap();

                    match (amount, address, script_hash) {
                        (
                            VmTerm::Signed128(amount),
                            VmTerm::Hash160(addr),
                            VmTerm::Hash160(script_hash),
                        ) if amount > 0 => {
                            let address = Address(addr);
                            let script_hash = Hash160(script_hash);

                            if let Some(idx) =
                                output_stack_idx_map.get(&(address.clone(), script_hash.clone()))
                            {
                                // Re-hash inputs
                                let inputs_hashes: Vec<u8> = vec![
                                    output_stack[*idx as usize].inputs_hash.clone(),
                                    inputs_hash.clone(),
                                ]
                                .iter()
                                .fold(vec![], |mut acc, hash| {
                                    acc.extend(hash.0);
                                    acc
                                });

                                let inputs_hash = Hash160::hash_from_slice(inputs_hashes, key);

                                output_stack[*idx as usize].amount += amount;
                                output_stack[*idx as usize].inputs_hash = inputs_hash;
                                output_stack[*idx as usize].compute_hash(key);
                                output_stack[*idx as usize].script_outs = script_outputs.clone();

                                *script_outputs = vec![];
                            } else {
                                let mut output = Output {
                                    amount,
                                    address: Some(address.clone()),
                                    script_hash: script_hash.clone(),
                                    coinbase_height: None,
                                    coloured_address: None,
                                    inputs_hash: inputs_hash.clone(),
                                    idx: output_stack.len() as u16,
                                    script_outs: script_outputs.clone(),
                                    hash: None,
                                };

                                output.compute_hash(key);
                                output_stack_idx_map
                                    .insert((address, script_hash), output_stack.len() as u16);
                                output_stack.push(output);
                                *script_outputs = vec![];

                                if output_stack.len() > MAX_OUT_STACK {
                                    self.state = ScriptExecutorState::Error(
                                        ExecutionResult::OutStackOverflow,
                                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                                    );
                                    return;
                                }
                            }

                            self.state = ScriptExecutorState::OkVerify;
                        }

                        _ => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::PushCoinbaseOut) => {
                    if exec_stack.len() < 4 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let amount = exec_stack.pop().unwrap();
                    *memory_size -= amount.size();
                    let address = exec_stack.pop().unwrap();
                    *memory_size -= address.size();
                    let script_hash = exec_stack.pop().unwrap();
                    *memory_size -= script_hash.size();
                    let coinbase_height = exec_stack.pop().unwrap();
                    *memory_size -= coinbase_height.size();

                    match (amount, address, script_hash, coinbase_height) {
                        (
                            VmTerm::Signed128(amount),
                            VmTerm::Hash160(addr),
                            VmTerm::Hash160(script_hash),
                            VmTerm::Unsigned64(coinbase_height),
                        ) if amount > 0 && coinbase_height > 0 => {
                            let mut output = Output {
                                amount,
                                address: Some(Address(addr)),
                                script_hash: Hash160(script_hash),
                                coinbase_height: Some(coinbase_height),
                                coloured_address: None,
                                inputs_hash: inputs_hash.clone(),
                                idx: output_stack.len() as u16,
                                script_outs: script_outputs.clone(),
                                hash: None,
                            };

                            output.compute_hash(key);
                            output_stack.push(output);
                            *script_outputs = vec![];

                            self.state = ScriptExecutorState::ExpectingInitialOP;
                        }

                        _ => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Verify) => {
                    self.state = ScriptExecutorState::OkVerify;
                }

                ScriptEntry::Opcode(OP::Loop) => {
                    self.state = ScriptExecutorState::NewLoopFrame;
                }

                ScriptEntry::Opcode(OP::Break) => {
                    self.state = ScriptExecutorState::BreakLoop;
                }

                ScriptEntry::Opcode(OP::BreakIf) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let top = exec_stack.pop().unwrap();
                    *memory_size -= top.size();

                    if top.equals_1() {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfn) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let top = exec_stack.pop().unwrap();
                    *memory_size -= top.size();

                    if !top.equals_1() {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfEq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 == e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfNeq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 != e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfLeq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 <= e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfGeq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 >= e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfLt) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 < e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::BreakIfGt) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 > e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::Continue) => {
                    self.state = ScriptExecutorState::ContinueLoop;
                }

                ScriptEntry::Opcode(OP::ContinueIf) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let top = exec_stack.pop().unwrap();
                    *memory_size -= top.size();

                    if top.equals_1() {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfn) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let top = exec_stack.pop().unwrap();
                    *memory_size -= top.size();

                    if !top.equals_1() {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfEq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 == e2 {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfNeq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 != e2 {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfLeq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 <= e2 {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfGeq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 >= e2 {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfLt) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 < e2 {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::ContinueIfGt) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 > e2 {
                        self.state = ScriptExecutorState::ContinueLoop;
                    } else {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::End) => {
                    self.state = ScriptExecutorState::EndBlock;
                }

                ScriptEntry::Opcode(OP::Depth) => {
                    exec_stack.push(VmTerm::Unsigned16(exec_stack.len() as u16));
                    *memory_size += 2;
                }

                ScriptEntry::Opcode(OP::IfDup) => {
                    let len = exec_stack.len();
                    if len == 0 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if !exec_stack[len - 1].equals_0() {
                        let c = exec_stack[len - 1].clone();
                        *memory_size += c.size();
                        exec_stack.push(c);
                    }
                }

                ScriptEntry::Opcode(OP::Drop) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }
                    let e = exec_stack.pop().unwrap();
                    *memory_size -= e.size();

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                ScriptEntry::Opcode(OP::Dup) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let c = exec_stack[exec_stack.len() - 1].clone();
                    *memory_size += c.size();
                    exec_stack.push(c);

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                ScriptEntry::Opcode(OP::Nip) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let r = exec_stack.remove(exec_stack.len() - 2);
                    *memory_size -= r.size();

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                ScriptEntry::Opcode(OP::Over) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let c = exec_stack[exec_stack.len() - 2].clone();
                    *memory_size += c.size();
                    exec_stack.push(c);

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                ScriptEntry::Opcode(OP::Pick) => {
                    self.state = ScriptExecutorState::ExpectingIndexU8(OP::Pick);
                }

                ScriptEntry::Opcode(OP::Roll) => {
                    self.state = ScriptExecutorState::ExpectingIndexU8(OP::Roll);
                }

                ScriptEntry::Opcode(OP::Rot) => {
                    if exec_stack.len() < 3 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let len = exec_stack.len();

                    unsafe {
                        // Similar implemenetation like in case of Rot2:
                        //
                        // Let's suppose we have the following items on the stack:
                        // [0, 1, 2]
                        //
                        // We first swap the pointers of the first elem and the last elem:
                        // [2, 1, 0]
                        exec_stack.swap_unchecked(len - 1, len - 3);

                        // We then swap the second and third elements:
                        // [1, 2, 0]
                        exec_stack.swap_unchecked(len - 2, len - 3);
                    }
                }

                ScriptEntry::Opcode(OP::Swap) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let len = exec_stack.len();

                    unsafe {
                        exec_stack.swap_unchecked(len - 1, len - 2);
                    }
                }

                ScriptEntry::Opcode(OP::Tuck) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e = exec_stack[exec_stack.len() - 1].clone();
                    *memory_size += e.size();
                    exec_stack.insert(exec_stack.len() - 2, e);
                }

                ScriptEntry::Opcode(OP::Drop2) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }
                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();
                }

                ScriptEntry::Opcode(OP::Dup2) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let c1 = exec_stack[exec_stack.len() - 1].clone();
                    let c2 = exec_stack[exec_stack.len() - 2].clone();

                    *memory_size += c1.size();
                    *memory_size += c2.size();

                    exec_stack.push(c2);
                    exec_stack.push(c1);
                }

                ScriptEntry::Opcode(OP::Dup3) => {
                    if exec_stack.len() < 3 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let c1 = exec_stack[exec_stack.len() - 1].clone();
                    let c2 = exec_stack[exec_stack.len() - 2].clone();
                    let c3 = exec_stack[exec_stack.len() - 3].clone();

                    *memory_size += c1.size();
                    *memory_size += c2.size();
                    *memory_size += c3.size();

                    exec_stack.push(c3);
                    exec_stack.push(c2);
                    exec_stack.push(c1);
                }

                ScriptEntry::Opcode(OP::Over2) => {
                    if exec_stack.len() < 4 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let c1 = exec_stack[exec_stack.len() - 3].clone();
                    let c2 = exec_stack[exec_stack.len() - 4].clone();

                    *memory_size += c1.size();
                    *memory_size += c2.size();

                    exec_stack.push(c2);
                    exec_stack.push(c1);
                }

                ScriptEntry::Opcode(OP::Rot2) => {
                    if exec_stack.len() < 6 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let len = exec_stack.len();

                    unsafe {
                        // Fastest implemenetation I can think of:
                        //
                        // Let's suppose we have the following items on the stack:
                        // [0, 1, 2, 3, 4, 5]
                        //
                        // We first swap the pointers of the first two elems and the last two:
                        // [4, 5, 2, 3, 0, 1]
                        exec_stack.swap_unchecked(len - 1, len - 5);
                        exec_stack.swap_unchecked(len - 2, len - 6);

                        // We then swap the third and fourth elements with the last two:
                        // [2, 3, 4, 5, 0, 1]
                        exec_stack.swap_unchecked(len - 3, len - 5);
                        exec_stack.swap_unchecked(len - 4, len - 6);
                    }
                }

                ScriptEntry::Opcode(OP::Swap2) => {
                    if exec_stack.len() < 4 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let len = exec_stack.len();

                    unsafe {
                        exec_stack.swap_unchecked(len - 1, len - 3);
                        exec_stack.swap_unchecked(len - 2, len - 4);
                    }
                }

                ScriptEntry::Opcode(OP::Size) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let size = exec_stack[exec_stack.len() - 1].size();
                    let e = VmTerm::Unsigned64(size as u64);

                    *memory_size += e.size();
                    exec_stack.push(e);
                }

                ScriptEntry::Opcode(OP::RandomHash160Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomHash160Var);
                }

                ScriptEntry::Opcode(OP::RandomHash256Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomHash256Var);
                }

                ScriptEntry::Opcode(OP::RandomHash512Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomHash512Var);
                }

                ScriptEntry::Opcode(OP::RandomUnsigned8Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned8Var);
                }

                ScriptEntry::Opcode(OP::RandomUnsigned16Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned16Var);
                }

                ScriptEntry::Opcode(OP::RandomUnsigned32Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned32Var);
                }

                ScriptEntry::Opcode(OP::RandomUnsigned64Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned64Var);
                }

                ScriptEntry::Opcode(OP::RandomUnsigned128Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomUnsigned128Var);
                }

                ScriptEntry::Opcode(OP::RandomSigned8Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned8Var);
                }

                ScriptEntry::Opcode(OP::RandomSigned16Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned16Var);
                }

                ScriptEntry::Opcode(OP::RandomSigned32Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned32Var);
                }

                ScriptEntry::Opcode(OP::RandomSigned64Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned64Var);
                }

                ScriptEntry::Opcode(OP::RandomSigned128Var) => {
                    self.state = ScriptExecutorState::ExpectingRandomTerm(OP::RandomSigned128Var);
                }

                ScriptEntry::Opcode(OP::Hash160Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash160Var);
                }

                ScriptEntry::Opcode(OP::Hash256Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash256Var);
                }

                ScriptEntry::Opcode(OP::Hash512Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash512Var);
                }

                ScriptEntry::Opcode(OP::Unsigned8Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8Var);
                }

                ScriptEntry::Opcode(OP::Unsigned16Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned16Var);
                }

                ScriptEntry::Opcode(OP::Unsigned32Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned32Var);
                }

                ScriptEntry::Opcode(OP::Unsigned64Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned64Var);
                }

                ScriptEntry::Opcode(OP::Unsigned128Var) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned128Var);
                }

                ScriptEntry::Opcode(OP::UnsignedBigVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::UnsignedBigVar);
                }

                ScriptEntry::Opcode(OP::Signed8Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed8Var);
                }

                ScriptEntry::Opcode(OP::Signed16Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed16Var);
                }

                ScriptEntry::Opcode(OP::Signed32Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed32Var);
                }

                ScriptEntry::Opcode(OP::Signed64Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed64Var);
                }

                ScriptEntry::Opcode(OP::Signed128Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed128Var);
                }

                ScriptEntry::Opcode(OP::SignedBigVar) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::SignedBigVar);
                }

                ScriptEntry::Opcode(OP::Unsigned8ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8ArrayVar);
                }

                ScriptEntry::Opcode(OP::Unsigned16ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned16ArrayVar);
                }

                ScriptEntry::Opcode(OP::Unsigned32ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned32ArrayVar);
                }

                ScriptEntry::Opcode(OP::Unsigned64ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned64ArrayVar);
                }

                ScriptEntry::Opcode(OP::Unsigned128ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned128ArrayVar);
                }

                ScriptEntry::Opcode(OP::UnsignedBigArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::UnsignedBigArrayVar);
                }

                ScriptEntry::Opcode(OP::Signed8ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed8ArrayVar);
                }

                ScriptEntry::Opcode(OP::Signed16ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed16ArrayVar);
                }

                ScriptEntry::Opcode(OP::Signed32ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed32ArrayVar);
                }

                ScriptEntry::Opcode(OP::Signed64ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed64ArrayVar);
                }

                ScriptEntry::Opcode(OP::Signed128ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Signed128ArrayVar);
                }

                ScriptEntry::Opcode(OP::SignedBigArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::SignedBigArrayVar);
                }

                ScriptEntry::Opcode(OP::ArrayLen) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let mut last = exec_stack.last_mut().unwrap();

                    if !last.is_array() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e = VmTerm::Unsigned16(last.len() as u16);

                    *memory_size += e.size();
                    exec_stack.push(e);
                }

                ScriptEntry::Opcode(OP::Add1) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let mut last = exec_stack.last_mut().unwrap();
                    if last.add_one().is_none() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::Sub1) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let mut last = exec_stack.last_mut().unwrap();
                    if last.sub_one().is_none() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::PopToScriptOuts) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e = exec_stack.pop().unwrap();
                    *memory_size -= e.size();
                    script_outputs.push(e);

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                ScriptEntry::Opcode(OP::PickToScriptOuts) => {
                    self.state = ScriptExecutorState::ExpectingIndexU8(OP::PickToScriptOuts);
                }

                ScriptEntry::Opcode(OP::Lt) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 < e2 {
                        exec_stack.push(VmTerm::Unsigned8(1));
                        *memory_size += 1;
                    } else {
                        exec_stack.push(VmTerm::Unsigned8(0));
                        *memory_size += 1;
                    }
                }

                ScriptEntry::Opcode(OP::Gt) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 > e2 {
                        exec_stack.push(VmTerm::Unsigned8(1));
                        *memory_size += 1;
                    } else {
                        exec_stack.push(VmTerm::Unsigned8(0));
                        *memory_size += 1;
                    }
                }

                ScriptEntry::Opcode(OP::Leq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 <= e2 {
                        exec_stack.push(VmTerm::Unsigned8(1));
                        *memory_size += 1;
                    } else {
                        exec_stack.push(VmTerm::Unsigned8(0));
                        *memory_size += 1;
                    }
                }

                ScriptEntry::Opcode(OP::Geq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let e1 = exec_stack.pop().unwrap();
                    *memory_size -= e1.size();
                    let e2 = exec_stack.pop().unwrap();
                    *memory_size -= e2.size();

                    if !e1.is_comparable(&e2) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if e1 >= e2 {
                        exec_stack.push(VmTerm::Unsigned8(1));
                        *memory_size += 1;
                    } else {
                        exec_stack.push(VmTerm::Unsigned8(0));
                        *memory_size += 1;
                    }
                }

                ScriptEntry::Opcode(OP::GetType) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let tp = exec_stack[exec_stack.len() - 1].get_type();
                    exec_stack.push(VmTerm::Unsigned8(tp));
                    *memory_size += 1;
                }

                ScriptEntry::Opcode(OP::ClearStack) => {
                    exec_stack.clear();
                }

                ScriptEntry::Opcode(OP::Trap) => {
                    self.state = ScriptExecutorState::Error(
                        ExecutionResult::Panic,
                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                    );
                }

                ScriptEntry::Opcode(OP::Ripemd160) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::ripemd160(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Sha256) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::sha256(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Sha512) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::sha512(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Keccak256) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::keccak256(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Keccak512) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::keccak512(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Blake2b256) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::blake2b_256(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Blake2b512) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::blake2b_512(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_256) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::blake3_256(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_512) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::blake3_512(&val);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_256Internal) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::blake3_256_internal(&val, key);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_512Internal) => {
                    match exec_stack.pop() {
                        Some(val) => {
                            *memory_size -= val.size();

                            let hash_term = bifs::blake3_512_internal(&val, key);

                            *memory_size += hash_term.size();
                            exec_stack.push(hash_term);
                        },
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        },
                    }
                }

                ScriptEntry::Opcode(_) => {
                    self.state = ScriptExecutorState::Error(
                        ExecutionResult::BadFormat,
                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                    );
                }
            }
            _ => unimplemented!(),
        }
    }

    #[inline]
    pub fn done(&self) -> Option<Result<ExecutionResult, (ExecutionResult, StackTrace)>> {
        match &self.state {
            ScriptExecutorState::OkVerify => Some(Ok(ExecutionResult::OkVerify)),
            ScriptExecutorState::Error(res, trace) => Some(Err((*res, trace.clone()))),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
enum ScriptExecutorState<'a> {
    /// Expecting script arguments length
    ExpectingArgsLen,

    /// Expecting any valid opcode in the default state
    ExpectingInitialOP,

    /// Expecting bytes or a cached term
    ExpectingBytesOrCachedTerm(OP),

    /// Expecting random term
    ExpectingRandomTerm(OP),

    /// Expecting specific opcodes
    ExpectingInitialOPorOPs(&'a [OP]),

    /// Expecting an u8 index for an opcode
    ExpectingIndexU8(OP),

    /// A new frame should be pushed to the stack and marked as loop
    NewLoopFrame,

    /// The current block has reached the final execution state
    EndBlock,

    /// Break the current loop
    BreakLoop,

    /// Continue to the next iteration of the current loop
    ContinueLoop,

    /// Return success error code and push message and signature to the verification stack
    OkVerify,

    /// Error
    Error(ExecutionResult, StackTrace),
}

impl Encode for Script {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.version, encoder)?;
        bincode::Encode::encode(&self.script.len(), encoder)?;

        for e in self.script.iter() {
            match e {
                ScriptEntry::Opcode(op) => {
                    bincode::Encode::encode(&op.to_u8().unwrap(), encoder)?;
                }

                ScriptEntry::Byte(byte) => {
                    bincode::Encode::encode(byte, encoder)?;
                }
            }
        }

        Ok(())
    }
}

impl Decode for Script {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let version: u8 = bincode::Decode::decode(decoder)?;
        let len: u16 = bincode::Decode::decode(decoder)?;
        let len = len as usize;
        let mut script_parser = ScriptParser::new(len);

        for _ in 0..len {
            let byte: u8 = bincode::Decode::decode(decoder)?;

            script_parser
                .push_byte(byte)
                .map_err(|err| bincode::error::DecodeError::OtherString(err.to_owned()))?;
        }

        Ok(Self {
            version,
            script: script_parser.out(),
        })
    }
}

struct ScriptParser {
    state: ScriptParserState,
    out: Vec<ScriptEntry>,
}

impl ScriptParser {
    pub fn new(len: usize) -> Self {
        Self {
            state: ScriptParserState::ExpectingFuncOrArgsLen,
            out: Vec::with_capacity(len),
        }
    }

    pub fn push_byte(&mut self, byte: u8) -> Result<(), &'static str> {
        match self.state {
            ScriptParserState::ExpectingFuncOrArgsLen => match OP::from_u8(byte) {
                Some(OP::Func) => {
                    self.out.push(ScriptEntry::Opcode(OP::Func));
                    self.state = ScriptParserState::ExpectingBytes(1);
                    Ok(())
                }

                _ => {
                    self.out.push(ScriptEntry::Byte(byte));
                    self.state = ScriptParserState::ExpectingOP;
                    Ok(())
                }
            },

            ScriptParserState::ExpectingOP => match OP::from_u8(byte) {
                Some(OP::Hash160Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Hash160Var));
                    self.state = ScriptParserState::ExpectingBytes(20);
                    Ok(())
                }
                Some(OP::Hash256Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Hash256Var));
                    self.state = ScriptParserState::ExpectingBytes(32);
                    Ok(())
                }
                Some(OP::Hash512Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Hash512Var));
                    self.state = ScriptParserState::ExpectingBytes(64);
                    Ok(())
                }
                Some(OP::Unsigned8Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned8Var));
                    self.state = ScriptParserState::ExpectingBytes(1);
                    Ok(())
                }
                Some(OP::Unsigned16Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned16Var));
                    self.state = ScriptParserState::ExpectingBytes(2);
                    Ok(())
                }
                Some(OP::Unsigned32Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned32Var));
                    self.state = ScriptParserState::ExpectingBytes(4);
                    Ok(())
                }
                Some(OP::Unsigned64Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned64Var));
                    self.state = ScriptParserState::ExpectingBytes(8);
                    Ok(())
                }
                Some(OP::Unsigned128Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned128Var));
                    self.state = ScriptParserState::ExpectingBytes(16);
                    Ok(())
                }
                Some(OP::UnsignedBigVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::UnsignedBigVar));
                    self.state = ScriptParserState::ExpectingBytes(32);
                    Ok(())
                }
                Some(OP::Signed8Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed8Var));
                    self.state = ScriptParserState::ExpectingBytes(1);
                    Ok(())
                }
                Some(OP::Signed16Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed16Var));
                    self.state = ScriptParserState::ExpectingBytes(2);
                    Ok(())
                }
                Some(OP::Signed32Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed32Var));
                    self.state = ScriptParserState::ExpectingBytes(4);
                    Ok(())
                }
                Some(OP::Signed64Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed64Var));
                    self.state = ScriptParserState::ExpectingBytes(8);
                    Ok(())
                }
                Some(OP::Signed128Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed128Var));
                    self.state = ScriptParserState::ExpectingBytes(16);
                    Ok(())
                }
                Some(OP::SignedBigVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::SignedBigVar));
                    self.state = ScriptParserState::ExpectingBytes(32);
                    Ok(())
                }
                Some(OP::Hash160ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Hash160ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Hash160ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Hash256ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Hash256ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Hash256ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Hash512ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Hash512ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Hash512ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Unsigned8ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned8ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Unsigned8ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Unsigned16ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned16ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Unsigned16ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Unsigned32ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned32ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Unsigned32ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Unsigned64ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned64ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Unsigned64ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Unsigned128ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Unsigned128ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Unsigned128ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::UnsignedBigArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::UnsignedBigArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::UnsignedBigArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Signed8ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed8ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Signed8ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Signed16ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed16ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Signed16ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Signed32ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed32ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Signed32ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Signed64ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed64ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Signed64ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::Signed128ArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::Signed128ArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::Signed128ArrayVar, 0, 0);
                    Ok(())
                }
                Some(OP::SignedBigArrayVar) => {
                    self.out.push(ScriptEntry::Opcode(OP::SignedBigArrayVar));
                    self.state = ScriptParserState::ExpectingLen(OP::SignedBigArrayVar, 0, 0);
                    Ok(())
                }
                Some(op) => {
                    self.out.push(ScriptEntry::Opcode(op));
                    Ok(())
                }
                None => Err("invalid op"),
            },

            ScriptParserState::ExpectingBytes(ref mut i) => {
                self.out.push(ScriptEntry::Byte(byte));
                *i -= 1;

                if *i == 0 {
                    self.state = ScriptParserState::ExpectingOP;
                }

                Ok(())
            }

            ScriptParserState::ExpectingLen(op, ref mut sum, ref mut i) => {
                self.out.push(ScriptEntry::Byte(byte));
                let b = byte as u16;
                if *i == 0 {
                    *sum += b;
                } else {
                    *sum += b << 8;
                }
                *i += 1;

                if *i == 2 {
                    match op {
                        OP::Hash160ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 20) as usize);
                            Ok(())
                        }
                        OP::Hash256ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 32) as usize);
                            Ok(())
                        }
                        OP::Hash512ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 64) as usize);
                            Ok(())
                        }
                        OP::Unsigned8ArrayVar | OP::Signed8ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum) as usize);
                            Ok(())
                        }
                        OP::Unsigned16ArrayVar | OP::Signed16ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 2) as usize);
                            Ok(())
                        }
                        OP::Unsigned32ArrayVar | OP::Signed32ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 4) as usize);
                            Ok(())
                        }
                        OP::Unsigned64ArrayVar | OP::Signed64ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 8) as usize);
                            Ok(())
                        }
                        OP::Unsigned128ArrayVar | OP::Signed128ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 16) as usize);
                            Ok(())
                        }
                        OP::UnsignedBigArrayVar | OP::SignedBigArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 32) as usize);
                            Ok(())
                        }
                        _ => unreachable!(),
                    }
                } else {
                    Ok(())
                }
            }
        }
    }

    pub fn out(self) -> Vec<ScriptEntry> {
        self.out
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct StackTrace {
    pub trace: Vec<TraceItem>,
    pub top_frame_stack: Vec<VmTerm>,
}

impl StackTrace {
    pub fn extend_from_frame_stack(&mut self, stack: &[Frame<'_>], script: &Script) {
        let trace = stack.iter().rev().take(TRACE_SIZE).map(|frame| TraceItem {
            i_ptr: frame.i_ptr,
            func_idx: frame.func_idx,
            entry: script.script[frame.i_ptr].clone(),
        });

        self.trace.extend(trace);
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraceItem {
    pub(crate) func_idx: usize,
    pub(crate) i_ptr: usize,
    pub(crate) entry: ScriptEntry,
}

impl From<(usize, usize, ScriptEntry, &[VmTerm])> for StackTrace {
    fn from(
        (i_ptr, func_idx, entry, top_frame_stack): (usize, usize, ScriptEntry, &[VmTerm]),
    ) -> Self {
        let ti = TraceItem {
            i_ptr,
            func_idx,
            entry,
        };

        Self {
            trace: vec![ti],
            top_frame_stack: top_frame_stack
                .iter()
                .rev()
                .take(TRACE_SIZE)
                .cloned()
                .collect(),
        }
    }
}

impl From<(usize, usize, OP, &[VmTerm])> for StackTrace {
    fn from((i_ptr, func_idx, entry, top_frame_stack): (usize, usize, OP, &[VmTerm])) -> Self {
        (i_ptr, func_idx, ScriptEntry::Opcode(entry), top_frame_stack).into()
    }
}

impl From<(usize, usize, OP)> for TraceItem {
    fn from((i_ptr, func_idx, entry): (usize, usize, OP)) -> Self {
        (i_ptr, func_idx, ScriptEntry::Opcode(entry)).into()
    }
}

impl From<(usize, usize, ScriptEntry)> for TraceItem {
    fn from((i_ptr, func_idx, entry): (usize, usize, ScriptEntry)) -> Self {
        Self {
            i_ptr,
            func_idx,
            entry,
        }
    }
}

// Don't compare stack traces
impl PartialEq for VmResult {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Ok(res1), Ok(res2)) => res1 == res2,
            (Err((res1, _)), Err((res2, _))) => res1 == res2,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct VmResult(Result<ExecutionResult, (ExecutionResult, StackTrace)>);

impl VmResult {
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }

    pub fn is_err(&self) -> bool {
        self.0.is_err()
    }

    pub fn to_inner(self) -> Result<ExecutionResult, (ExecutionResult, StackTrace)> {
        self.0
    }
}

impl From<Result<ExecutionResult, (ExecutionResult, StackTrace)>> for VmResult {
    fn from(other: Result<ExecutionResult, (ExecutionResult, StackTrace)>) -> Self {
        Self(other)
    }
}

enum ScriptParserState {
    ExpectingFuncOrArgsLen,
    ExpectingOP,
    ExpectingBytes(usize),
    ExpectingLen(OP, u16, usize),
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum ScriptErr {
    InvalidOpcode,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum ExecutionResult {
    /// Execution was successful
    Ok,

    /// Execution was successful but requires signature verification
    OkVerify,

    /// Invalid script execution result
    Invalid,

    /// Invalid arguments on the stack
    InvalidArgs,

    /// Invalid script format
    BadFormat,

    /// Stack overflow
    StackOverflow,

    /// Output stack overflow
    OutStackOverflow,

    /// VM ran out of memory
    OutOfMemory,

    /// VM ran out of gas
    OutOfGas,

    /// VM Term overflow
    TermOverflow,

    /// Bad script version
    BadVersion,

    /// Too many arguments given
    TooManyArgs,

    /// The provided index is out of bounds
    IndexOutOfBounds,

    /// Explicit panic
    Panic,
}

#[cfg(test)]
mod tests {
    use std::string;

    use super::*;
    use crate::consensus::Money;
    use rayon::prelude::*;

    pub struct TestBaseArgs {
        args: Vec<VmTerm>,
        ins: Vec<Input>,
        out: Vec<Output>,
    }

    fn get_test_base_args(
        ss: &Script,
        out_amount: Money,
        out_script: Vec<VmTerm>,
        push_out_cycles: usize,
        key: &str,
    ) -> TestBaseArgs {
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

        // Prepare output
        let ins_hashes: Vec<u8> = ins.iter_mut().fold(vec![], |mut acc, v: &mut Input| {
            v.compute_hash(key);
            acc.extend(v.hash().unwrap().0);
            acc
        });
        let inputs_hash = Hash160::hash_from_slice(ins_hashes.as_slice(), key);
        let inputs_hash: Hash160 = ins.iter().cloned().cycle().take(push_out_cycles).fold(
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
            amount: out_amount,
            script_hash: sh,
            inputs_hash,
            coloured_address: None,
            coinbase_height: None,
            hash: None,
            script_outs: out_script,
            idx: 0,
        };
        oracle_out.compute_hash(key);

        TestBaseArgs {
            args,
            ins,
            out: vec![oracle_out],
        }
    }

    #[test]
    fn it_simple_spends() {
        let key = "test_key";
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
        let mut idx_map = HashMap::new();
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
        }];
        let mut outs = vec![];

        let ins_hashes: Vec<u8> = ins.iter_mut().fold(vec![], |mut acc, v: &mut Input| {
            v.compute_hash(key);
            acc.extend(v.hash().unwrap().0);
            acc
        });

        let inputs_hash = Hash160::hash_from_slice(ins_hashes, key);
        let mut oracle_out = Output {
            address: Some(Hash160::zero().to_address()),
            amount: 30,
            script_hash: sh,
            inputs_hash,
            coloured_address: None,
            coinbase_height: None,
            hash: None,
            script_outs: vec![],
            idx: 0,
        };
        oracle_out.compute_hash(key);

        assert_eq!(
            ss.execute(
                &args,
                &ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, vec![oracle_out]);
    }

    #[test]
    fn it_breaks_loop_if_values_equal() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfEq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };
        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_values_not_equal() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::BreakIfNeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 60, vec![], 1, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_equal_to_1() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::BreakIf),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_not_equal_to_1() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::BreakIfn),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 60, vec![], 1, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_values_equal_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfEq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_less_or_equal() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfLeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_less_or_equal_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::BreakIfLeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_greater_or_equal() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfGeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_greater_or_equal_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfGeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_less() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfLt),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_less_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::BreakIfLt),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_greater() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfGt),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_breaks_loop_if_greater_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::BreakIfGt),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_less_or_equal() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::ContinueIfLeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_less_or_equal_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x0a),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::ContinueIfLeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_greater_or_equal() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::ContinueIfGeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_greater_or_equal_test_2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x07),
                ScriptEntry::Opcode(OP::ContinueIfGeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_less() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::ContinueIfLt),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_greater() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::ContinueIfGt),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_equals_1() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::ContinueIf),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 60, vec![], 1, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_not_equals_1() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Sub1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::ContinueIfn),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 90, vec![], 2, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_equals() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::ContinueIfEq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 60, vec![], 1, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_continues_loop_if_not_equals() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::ContinueIfNeq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 120, vec![], 3, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_runs_out_of_gas() {
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
        let mut idx_map = HashMap::new();
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

        let mut outs = vec![];
        assert_eq!(
            ss.execute(
                &args,
                ins.as_slice(),
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::OutOfGas, StackTrace::default())).into()
        );
    }

    #[test]
    fn pushout_zero_amount() {
        let key = "test_key";
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
        let mut idx_map = HashMap::new();
        let args = vec![
            VmTerm::Signed128(0),
            VmTerm::Hash160([0; 20]),
            VmTerm::Hash160(sh.0),
        ];
        let mut ins: Vec<Input> = vec![Input {
            out: None,
            spend_proof: None,
            colour_proof: None,
            colour_proof_without_address: None,
            colour_script_args: None,
            colour_script: None,
            spending_pkey: None,
            witness: None,
            script: ss.clone(),
            nsequence: 0xffffffff,
            script_args: args.clone(),
            hash: None,
        }]
        .iter()
        .cloned()
        .map(|mut i| {
            i.compute_hash(key);
            i
        })
        .collect();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &args,
                &ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn pushout_neg_amount() {
        let key = "test_key";
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
        let mut idx_map = HashMap::new();
        let args = vec![
            VmTerm::Signed128(-30),
            VmTerm::Hash160([0; 20]),
            VmTerm::Hash160(sh.0),
        ];
        let mut ins: Vec<Input> = vec![Input {
            out: None,
            spend_proof: None,
            colour_proof: None,
            colour_proof_without_address: None,
            colour_script_args: None,
            colour_script: None,
            spending_pkey: None,
            witness: None,
            nsequence: 0xffffffff,
            script: ss.clone(),
            script_args: args.clone(),
            hash: None,
        }]
        .iter()
        .cloned()
        .map(|mut i| {
            i.compute_hash(key);
            i
        })
        .collect();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &args,
                &ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_encodes_to_single_byte() {
        let script = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
            ],
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        assert_eq!(
            encoded,
            vec![0x01, 0x09, 0x01, 0x25, 0x00, 0x00, 0x00, 0x00, 0x24, 0x00, 0x00]
        );
    }

    #[test]
    fn it_encodes_to_single_byte_2() {
        let script = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
            ],
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        assert_eq!(
            encoded,
            vec![0x01, 0x09, 0x01, 0x25, 0xff, 0xff, 0xff, 0xff, 0x24, 0xff, 0xff]
        );
    }

    #[test]
    fn it_encodes_and_decodes() {
        let script = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
            ],
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        let decoded: Script = crate::codec::decode(&encoded).unwrap();
        assert_eq!(decoded, script);
    }

    #[test]
    fn it_encodes_and_decodes_coinbase() {
        let script = Script::new_coinbase();
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        let decoded: Script = crate::codec::decode(&encoded).unwrap();
        assert_eq!(decoded, script);
    }

    #[test]
    fn it_encodes_and_decodes_simple_spend() {
        let script = Script::new_simple_spend();
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        let decoded: Script = crate::codec::decode(&encoded).unwrap();
        assert_eq!(decoded, script);
    }

    #[test]
    fn it_encodes_and_decodes_2() {
        let script = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned32ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xf0),
                ScriptEntry::Byte(0xf0),
            ],
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        let decoded: Script = crate::codec::decode(&encoded).unwrap();
        assert_eq!(decoded, script);
    }

    #[test]
    fn it_roll_pop_out() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Roll),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Roll),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_roll_pick_out() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Roll),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Roll),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::PickToScriptOuts),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::PickToScriptOuts),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::PickToScriptOuts),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_depth() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x1),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x1),
                ScriptEntry::Opcode(OP::Depth),
                ScriptEntry::Opcode(OP::Depth),
                ScriptEntry::Opcode(OP::Depth),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(7),
            VmTerm::Unsigned16(6),
            VmTerm::Unsigned16(5),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_if_dup() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x0),
                ScriptEntry::Opcode(OP::IfDup),
                ScriptEntry::Opcode(OP::IfDup),
                ScriptEntry::Opcode(OP::IfDup),
                ScriptEntry::Opcode(OP::IfDup),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x1),
                ScriptEntry::Opcode(OP::IfDup),
                ScriptEntry::Opcode(OP::IfDup),
                ScriptEntry::Opcode(OP::Depth),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(7),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_dup() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_nip() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Nip),
                ScriptEntry::Opcode(OP::Nip),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8(4), VmTerm::Unsigned8(1)];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_rot() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Rot),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(5),
            VmTerm::Unsigned8(4),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_rot2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::Rot2),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
            VmTerm::Unsigned8(5),
            VmTerm::Unsigned8(4),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_over() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Over),
                ScriptEntry::Opcode(OP::Over2),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_swap() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Swap),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_swap2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::Swap2),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(5),
            VmTerm::Unsigned8(4),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_tuck() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Tuck),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_drop2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8(5)];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_dup2() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Dup2),
                ScriptEntry::Opcode(OP::Dup2),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_dup3() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Dup3),
                ScriptEntry::Opcode(OP::Dup3),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    // TODO: extend for all types when implemented
    #[test]
    fn it_adds_size() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Size),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned64(1), VmTerm::Unsigned8(0)];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_fails_drop_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_dup_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_nip_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Nip),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_rot_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Rot),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_rot_2_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Rot2),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_over_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Over),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_roll_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Roll),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::IndexOutOfBounds, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_swap_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Swap),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_tuck_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Tuck),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_drop_2_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_dup_2_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Dup2),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_dup_3_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Dup3),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_over_2_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x1),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x2),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x3),
                ScriptEntry::Opcode(OP::Over2),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_swap_2_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x1),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x2),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x3),
                ScriptEntry::Opcode(OP::Swap2),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_fails_to_push_size_when_stack_length_is_lower() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Size),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let base: TestBaseArgs = get_test_base_args(&ss, 30, vec![], 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((ExecutionResult::InvalidArgs, StackTrace::default())).into()
        );
    }

    #[test]
    fn it_loads_hash_160var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Hash160Var),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Opcode(OP::Hash160Var),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash160([
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
            ]),
            VmTerm::Hash160([
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_hash_256var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Hash256Var),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Opcode(OP::Hash256Var),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash256([
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47,
                0x35, 0x12, 0x18, 0x34,
            ]),
            VmTerm::Hash256([
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47,
                0x35, 0x12, 0x18, 0x34,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_hash_512var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Hash512Var),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Opcode(OP::Hash512Var),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x74),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x53),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x47),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x18),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash512([
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47,
                0x35, 0x12, 0x18, 0x34, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12,
                0x18, 0x34, 0x85, 0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23,
                0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
            ]),
            VmTerm::Hash512([
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47,
                0x35, 0x12, 0x18, 0x34, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12,
                0x18, 0x34, 0x85, 0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23,
                0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_8var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x11),
            VmTerm::Unsigned8(0x23),
            VmTerm::Unsigned8(0x01),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_16var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(0x0011),
            VmTerm::Unsigned16(0x2301),
            VmTerm::Unsigned16(0x0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_32var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(0x00000011),
            VmTerm::Unsigned32(0x00002301),
            VmTerm::Unsigned32(0x00000123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_64var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned64Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned64Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned64Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned64(0x0000000000000011),
            VmTerm::Unsigned64(0x0123000000002301),
            VmTerm::Unsigned64(0x0123000000000123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_128var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned128Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Opcode(OP::Unsigned128Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned128(0x22000000000000000123000000002301),
            VmTerm::Unsigned128(0x11000000000000000123000000000123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_16var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed16Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Signed16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Opcode(OP::Signed16Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed16(0x0011),
            VmTerm::Signed16(0x2301),
            VmTerm::Signed16(0x0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_32var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed32Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Signed32Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Signed32Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed32(0x00000011),
            VmTerm::Signed32(0x00002301),
            VmTerm::Signed32(0x00000123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_64var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed64Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Signed64Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Signed64Var),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed64(0x0000000000000011),
            VmTerm::Signed64(0x0123000000002301),
            VmTerm::Signed64(0x0123000000000123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_128var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed128Var),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Opcode(OP::Signed128Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed128(0x22000000000000000123000000002301),
            VmTerm::Signed128(0x11000000000000000123000000000123),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_8_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x3f),
                ScriptEntry::Byte(0x79),
                ScriptEntry::Byte(0x25),
                ScriptEntry::Byte(0xae),
                ScriptEntry::Byte(0x77),
                ScriptEntry::Byte(0xa1),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x3f, 0x79, 0x25, 0xae, 0x77, 0xa1]),
            VmTerm::Unsigned8Array(vec![0x75, 0xaf, 0xf6, 0xa5]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_16_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x3f),
                ScriptEntry::Byte(0x26),
                ScriptEntry::Byte(0x79),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Byte(0x25),
                ScriptEntry::Byte(0xbc),
                ScriptEntry::Byte(0xae),
                ScriptEntry::Byte(0x27),
                ScriptEntry::Byte(0x77),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0xa1),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16Array(vec![0x3ffe, 0x7926, 0x2510, 0xaebc, 0x7727, 0xa123]),
            VmTerm::Unsigned16Array(vec![0x7536, 0x7516, 0xaf41, 0xa5f6]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_32_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned32ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Opcode(OP::Unsigned32ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32Array(vec![
                0xa5f6af41, 0x75167536, 0x75167536, 0x75167536, 0x75167536, 0xa5f6af41,
            ]),
            VmTerm::Unsigned32Array(vec![0x01fe7814, 0x75167536, 0xa5f6af41, 0x75167536]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_64_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned64ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Opcode(OP::Unsigned64ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned64Array(vec![
                0xa5f6af41a5f6af41,
                0x7516753675167536,
                0x7516753675167536,
                0x7516753675167536,
                0x7516753675167536,
                0xa5f6af41a5f6af41,
            ]),
            VmTerm::Unsigned64Array(vec![
                0x01fe781401fe7814,
                0x7516753675167536,
                0xa5f6af41a5f6af41,
                0x7516753675167536,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_unsigned_128_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned128ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Opcode(OP::Unsigned128ArrayVar),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned128Array(vec![
                0x7516753675167536a5f6af41a5f6af41,
                0x75167536751675367516753675167536,
                0xa5f6af41a5f6af417516753675167536,
            ]),
            VmTerm::Unsigned128Array(vec![
                0x751675367516753601fe781401fe7814,
                0x7516753675167536a5f6af41a5f6af41,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_8_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed8ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x34),
                ScriptEntry::Byte(0x54),
                ScriptEntry::Opcode(OP::Signed8ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x3f),
                ScriptEntry::Byte(0x79),
                ScriptEntry::Byte(0x25),
                ScriptEntry::Byte(0x12),
                ScriptEntry::Byte(0x77),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed8Array(vec![0x3f, 0x79, 0x25, 0x12, 0x77, 0x11]),
            VmTerm::Signed8Array(vec![0x75, 0x12, 0x34, 0x54]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_16_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed16ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0x1f),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Opcode(OP::Signed16ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x3f),
                ScriptEntry::Byte(0x26),
                ScriptEntry::Byte(0x79),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Byte(0x25),
                ScriptEntry::Byte(0xbc),
                ScriptEntry::Byte(0x2e),
                ScriptEntry::Byte(0x27),
                ScriptEntry::Byte(0x77),
                ScriptEntry::Byte(0x23),
                ScriptEntry::Byte(0x11),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed16Array(vec![0x3ffe, 0x7926, 0x2510, 0x2ebc, 0x7727, 0x1123]),
            VmTerm::Signed16Array(vec![0x7536, 0x7516, 0x1f41, 0x15f6]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_32_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed32ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Opcode(OP::Signed32ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed32Array(vec![
                0x15f6af41, 0x75167536, 0x75167536, 0x75167536, 0x75167536, 0x15f6af41,
            ]),
            VmTerm::Signed32Array(vec![0x01fe7814, 0x75167536, 0x15f6af41, 0x75167536]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_64_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed64ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Opcode(OP::Signed64ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed64Array(vec![
                0x15f6af41a5f6af41,
                0x7516753675167536,
                0x7516753675167536,
                0x7516753675167536,
                0x7516753675167536,
                0x15f6af41a5f6af41,
            ]),
            VmTerm::Signed64Array(vec![
                0x01fe781401fe7814,
                0x7516753675167536,
                0x15f6af41a5f6af41,
                0x7516753675167536,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_loads_signed_128_array_var() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed128ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0xfe),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Opcode(OP::Signed128ArrayVar),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x16),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Byte(0x41),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0x15),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed128Array(vec![
                0x7516753675167536a5f6af41a5f6af41,
                0x75167536751675367516753675167536,
                0x15f6af41a5f6af417516753675167536,
            ]),
            VmTerm::Signed128Array(vec![
                0x751675367516753601fe781401fe7814,
                0x7516753675167536a5f6af41a5f6af41,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_pushes_array_len() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::ArrayLen),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x3f),
                ScriptEntry::Byte(0x79),
                ScriptEntry::Byte(0x25),
                ScriptEntry::Byte(0xae),
                ScriptEntry::Byte(0x77),
                ScriptEntry::Byte(0xa1),
                ScriptEntry::Opcode(OP::ArrayLen),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned16(0x0004), VmTerm::Unsigned16(0x0006)];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_gets_type() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash160Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomHash256Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomHash512Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomUnsigned8Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomUnsigned16Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomUnsigned32Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomUnsigned64Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomUnsigned128Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomSigned8Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomSigned16Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomSigned32Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomSigned64Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::RandomSigned128Var),
                ScriptEntry::Opcode(OP::GetType),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x02),
            VmTerm::Unsigned8(0x03),
            VmTerm::Unsigned8(0x04),
            VmTerm::Unsigned8(0x05),
            VmTerm::Unsigned8(0x06),
            VmTerm::Unsigned8(0x07),
            VmTerm::Unsigned8(0x09),
            VmTerm::Unsigned8(0x0a),
            VmTerm::Unsigned8(0x0b),
            VmTerm::Unsigned8(0x0c),
            VmTerm::Unsigned8(0x0d),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_160_hash() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash160Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomHash160Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash160(rng.gen::<[u8; 20]>()),
            VmTerm::Hash160(rng.gen::<[u8; 20]>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_256_hash() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash256Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomHash256Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash256(rng.gen::<[u8; 32]>()),
            VmTerm::Hash256(rng.gen::<[u8; 32]>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_512_hash() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash512Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomHash512Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let p1 = rng.gen::<[u8; 32]>();
        let p2 = rng.gen::<[u8; 32]>();
        let p3 = rng.gen::<[u8; 32]>();
        let p4 = rng.gen::<[u8; 32]>();

        let mut res1 = [0; 64];
        let mut res2 = [0; 64];

        res1[..32].copy_from_slice(&p1);
        res1[32..64].copy_from_slice(&p2);
        res2[..32].copy_from_slice(&p3);
        res2[32..64].copy_from_slice(&p4);

        let script_output: Vec<VmTerm> = vec![VmTerm::Hash512(res1), VmTerm::Hash512(res2)];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_unsigned_8var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(rng.gen::<u8>()),
            VmTerm::Unsigned8(rng.gen::<u8>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_unsigned_16var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(rng.gen::<u16>()),
            VmTerm::Unsigned16(rng.gen::<u16>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_unsigned_32var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(rng.gen::<u32>()),
            VmTerm::Unsigned32(rng.gen::<u32>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_unsigned_64var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned64(rng.gen::<u64>()),
            VmTerm::Unsigned64(rng.gen::<u64>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_unsigned_128var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned128(rng.gen::<u128>()),
            VmTerm::Unsigned128(rng.gen::<u128>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_signed_8var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed8(rng.gen::<i8>()),
            VmTerm::Signed8(rng.gen::<i8>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_signed_16var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed16(rng.gen::<i16>()),
            VmTerm::Signed16(rng.gen::<i16>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_signed_32var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed32(rng.gen::<i32>()),
            VmTerm::Signed32(rng.gen::<i32>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_signed_64var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed64(rng.gen::<i64>()),
            VmTerm::Signed64(rng.gen::<i64>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_generates_random_signed_128var() {
        let seed = [0; 32];
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed128(rng.gen::<i128>()),
            VmTerm::Signed128(rng.gen::<i128>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                seed,
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_pushes_1_if_lt_and_0_if_not() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Lt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Lt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Opcode(OP::Lt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Lt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_pushes_1_if_gt_and_0_if_not() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Opcode(OP::Gt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Gt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Gt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Gt),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_pushes_1_if_leq_and_0_if_not() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Leq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Leq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Leq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Leq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_pushes_1_if_geq_and_0_if_not() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Opcode(OP::Geq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Geq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Geq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Geq),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_hashes_with_ripemd() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Ripemd160),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Ripemd160),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify)
            ]
        };

        let test_terms = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Signed8(-1),
        ];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::ripemd160(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_hashes_with_sha256() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Sha256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Sha256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify)
            ]
        };

        let test_terms = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Signed8(-1),
        ];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::sha256(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_hashes_with_sha512() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Sha512),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Sha512),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify)
            ]
        };

        let test_terms = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Signed8(-1),
        ];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::sha512(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }

    #[test]
    fn it_hashes_with_blake2b() {
        let key = "test_key";
        let ss = Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake2b256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake2b256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake2b512),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake2b512),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify)
            ]
        };

        let test_terms = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Signed8(-1),
        ];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms.iter() {
            let hashed_term_256 = bifs::blake2b_256(&term);
            script_output.push(hashed_term_256);
        }
        for term in test_terms.iter() {
            let hashed_term_512 = bifs::blake2b_512(&term);
            script_output.push(hashed_term_512);
        }

        let base: TestBaseArgs = get_test_base_args(&ss, 30, script_output, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];

        assert_eq!(
            ss.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, base.out);
    }
}
