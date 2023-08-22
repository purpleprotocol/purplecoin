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
use bitvec::prelude::*;
use ibig::{ibig, ubig};
use num_traits::{FromPrimitive, ToPrimitive};
use rand::prelude::*;
use rand_pcg::Pcg64;
use rand_seeder::Seeder;
use simdutf8::basic::from_utf8;
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

#[derive(PartialEq, Debug, Clone)]
pub enum ScriptEntry {
    Opcode(OP),
    Byte(u8),
}

#[derive(Debug, Clone)]
pub struct Frame<'a> {
    /// Stack storing the terms on the current frame
    pub stack: Vec<VmTerm>,

    /// Instruction pointer
    pub i_ptr: usize,

    /// Func index. This is `None` if the current function is the main function
    pub func_idx: Option<usize>,

    /// Some((start_ip, end_ip)) if the current frame is a loop start_ip is the
    /// instruction pointer at the beginning of the loop and end_ip at the end.
    pub is_loop: Option<(usize, usize)>,

    /// Script executor
    pub executor: ScriptExecutor<'a>,
}

impl<'a> Frame<'a> {
    #[must_use]
    pub fn new(func_idx: Option<usize>) -> Self {
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

#[derive(PartialEq, Debug, Clone, Default)]
pub struct Script {
    /// Main script
    pub script: Vec<ScriptEntry>,

    /// Other functions in the script
    pub functions: Vec<Vec<ScriptEntry>>,

    /// For each argument, a boolean denoting whether the argument is malleable or not.
    ///
    /// A malleable argument is not signed by the spender.
    pub malleable_args: BitVec,
}

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

macro_rules! check_bit {
    ($val:expr, $pos:expr) => {
        $val & (1 << $pos) == 1
    };
}

macro_rules! set_bit {
    ($val:expr, $pos:expr, $to_set:expr) => {{
        (($val & (1 << $pos)) | ($to_set << $pos))
    }};
}

macro_rules! var_load {
    ($frame:expr, $script:expr, $sum:ident, $type:ty, $step:expr) => {
        $frame.i_ptr += 1;
        if let ScriptEntry::Byte(byte) = $script[$frame.i_ptr] {
            $sum += (byte as $type);
        } else {
            unreachable!()
        }
    };

    ($frame:expr, $script:expr, $sum:ident, $type:ty, $step:expr, $($tail:expr), +) => {
        var_load!($frame, $script, $sum, $type, $($tail), +);

        $frame.i_ptr += 1;
        if let ScriptEntry::Byte(byte) = $script[$frame.i_ptr] {
            $sum += (byte as $type) << $step;
        } else {
            unreachable!()
        }
    };
}

macro_rules! bitvec_from_bools {
    () => {{
        BitVec::new()
    }};

    ($($a:expr),+ $(,)?) => {{
        let mut buf = BitVec::new();
        $(
            buf.push($a);
        )+
        buf
    }};
}

impl Script {
    #[must_use]
    pub fn new_coinbase() -> Script {
        Script {
            script: vec![
                ScriptEntry::Byte(0x05), // 5 arguments are pushed onto the stack: out_amount, out_address, out_script_hash, coinbase_height, extra_nonce
                ScriptEntry::Opcode(OP::PushCoinbaseOut),
            ],
            malleable_args: bitvec_from_bools![false, false, false, false, false],
            ..Script::default()
        }
    }

    #[must_use]
    pub fn new_coinbase_without_spending_address() -> Script {
        Script {
            script: vec![
                ScriptEntry::Byte(0x04), // 4 arguments are pushed onto the stack: out_amount, out_script_hash, coinbase_height, extra_nonce
                ScriptEntry::Opcode(OP::PushCoinbaseOutNoSpendAddress),
            ],
            malleable_args: bitvec_from_bools![false, false, false, false],
            ..Script::default()
        }
    }

    #[must_use]
    pub fn new_simple_spend() -> Script {
        Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOutVerify),
            ],
            malleable_args: bitvec_from_bools![false, false, false],
            ..Script::default()
        }
    }

    /// Utility to populate `malleable_args` field in tests.
    pub fn populate_malleable_args_field(&mut self) {
        if self.malleable_args.is_empty() {
            assert!(!self.script.is_empty());
            if let ScriptEntry::Byte(byte) = self.script[0] {
                let num = byte as usize;
                self.malleable_args = (0..num).map(|_| false).collect();
            } else {
                unreachable!();
            }
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
        if args.len() > STACK_SIZE {
            return Err((
                ExecutionResult::TooManyArgs,
                StackTrace {
                    trace: vec![(0_usize, None, self.script[0].clone()).into()],
                    top_frame_stack: vec![],
                },
            ))
            .into();
        }

        // Seed RNG
        let mut rng: Pcg64 = Seeder::from(seed).make_rng();

        // Initialize internals
        let mut memory_size = 0;
        let mut exec_count = 0;
        let mut frame_stack: Vec<Frame> = Vec::with_capacity(MAX_FRAMES);
        let mut frame = Frame::new(None);
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
                let f = match frame.func_idx {
                    Some(func_idx) => &self.functions[func_idx],
                    None => &self.script,
                };

                if frame.i_ptr >= f.len() {
                    pop_frame = true;
                } else {
                    let i = &f[frame.i_ptr];

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

                            for t in &nf.stack {
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

                        ScriptExecutorState::ReturnFunc => {
                            pop_frame = true;
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

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Call) => {
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                let func_idx = *byte;
                                let func = &self.functions[func_idx as usize];
                                let mut nf = Frame::new(Some(func_idx as usize));
                                let args_len = &func[0];

                                if let ScriptEntry::Byte(args_len) = args_len {
                                    if frame.stack.len() < *args_len as usize {
                                        unimplemented!();
                                    }

                                    for _ in 0..*args_len {
                                        nf.stack.push(frame.stack.pop().unwrap());
                                    }
                                }
                                frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                                new_frame = Some(nf);
                            } else {
                                unreachable!()
                            }
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::TrapIfNeqType) => {
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                let e = frame.stack.pop().unwrap();
                                memory_size -= e.size();

                                if e.get_type() == *byte {
                                    frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                                    frame.i_ptr += 1;
                                } else {
                                    frame.executor.state = ScriptExecutorState::Error(
                                        ExecutionResult::Panic,
                                        (
                                            frame.i_ptr,
                                            frame.func_idx,
                                            i.clone(),
                                            frame.stack.as_slice(),
                                        )
                                            .into(),
                                    );
                                }
                            } else {
                                unreachable!()
                            }
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash160Var) => {
                            let mut arr: [u8; 20] = [0; 20];

                            for i in 0..20 {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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
                                if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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
                                if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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

                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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

                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash160ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<[u8; 20]> = Vec::new();
                            for _ in 0..len {
                                let mut hash_arr: [u8; 20] = [0; 20];

                                for i in 0..20 {
                                    frame.i_ptr += 1;
                                    if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                        hash_arr[i] = *byte;
                                    } else {
                                        unreachable!()
                                    }
                                }

                                arr.push(hash_arr);
                            }

                            let term = VmTerm::Hash160Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash256ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<[u8; 32]> = Vec::new();
                            for _ in 0..len {
                                let mut hash_arr: [u8; 32] = [0; 32];

                                for i in 0..32 {
                                    frame.i_ptr += 1;
                                    if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                        hash_arr[i] = *byte;
                                    } else {
                                        unreachable!()
                                    }
                                }

                                arr.push(hash_arr);
                            }

                            let term = VmTerm::Hash256Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash512ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<[u8; 64]> = Vec::new();
                            for _ in 0..len {
                                let mut hash_arr: [u8; 64] = [0; 64];

                                for i in 0..64 {
                                    frame.i_ptr += 1;
                                    if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                        hash_arr[i] = *byte;
                                    } else {
                                        unreachable!()
                                    }
                                }

                                arr.push(hash_arr);
                            }

                            let term = VmTerm::Hash512Array(arr);
                            memory_size += term.size();
                            frame.stack.push(term);
                            frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                            frame.i_ptr += 1;
                        }

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8ArrayVar) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<u8> = Vec::new();
                            for _ in 0..len {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
                            } else {
                                unreachable!()
                            }

                            let mut arr: Vec<i8> = Vec::new();
                            for _ in 0..len {
                                frame.i_ptr += 1;
                                if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
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

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Substr) => {
                            let mut len: u16 = 0;

                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte);
                            } else {
                                unreachable!()
                            }
                            frame.i_ptr += 1;
                            if let ScriptEntry::Byte(byte) = &f[frame.i_ptr] {
                                len += u16::from(*byte) << 8;
                            } else {
                                unreachable!()
                            }

                            let arr = frame.stack.pop().unwrap();
                            let mid = len as usize;

                            if mid > arr.len() {
                                frame.executor.state = ScriptExecutorState::Error(
                                    ExecutionResult::IndexOutOfBounds,
                                    (
                                        frame.i_ptr,
                                        frame.func_idx,
                                        i.clone(),
                                        frame.stack.as_slice(),
                                    )
                                        .into(),
                                );
                            } else {
                                let (left, right) = arr.split_at_unchecked(mid).unwrap();
                                frame.stack.push(left);
                                frame.stack.push(right);

                                // The items size is already added to the memory_size of the VM,
                                // we just only have to add the HEAP_SIZE for the second vector
                                memory_size += crate::vm::internal::EMPTY_VEC_HEAP_SIZE;

                                frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                                frame.i_ptr += 1;
                            }
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
                            check_top_stack_val!(v, frame, frame_stack, self, &flags);
                        }
                        VmTerm::Signed16(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags);
                        }
                        VmTerm::Signed32(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags);
                        }
                        VmTerm::Signed64(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags);
                        }
                        VmTerm::Signed128(v) => {
                            check_top_stack_val!(v, frame, frame_stack, self, &flags);
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

    #[must_use]
    pub fn to_script_hash(&self, key: &str) -> Hash160 {
        Hash160::hash_from_slice(crate::codec::encode_to_vec(&self).unwrap(), key)
    }
}

#[derive(Debug, Clone)]
pub struct ScriptExecutor<'a> {
    state: ScriptExecutorState<'a>,
}

impl<'a> ScriptExecutor<'a> {
    #[must_use]
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
        func_idx: Option<usize>,
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
                                let inputs_hashes: Vec<u8> = [
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
                                let inputs_hashes: Vec<u8> = [
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

                ScriptEntry::Opcode(OP::Call) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Call);
                }

                ScriptEntry::Opcode(OP::ReturnFunc) => {
                    if func_idx.is_some() {
                        self.state = ScriptExecutorState::ReturnFunc;
                    } else {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::BadFormat,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
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

                ScriptEntry::Opcode(OP::Substr) => {
                    let len = exec_stack.len();

                    if len == 0 || !exec_stack[len - 1].is_array() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Substr);
                }

                ScriptEntry::Opcode(OP::BitOR) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match last.or(&mut second) {
                        Some(_) => {
                            exec_stack.push(last);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::BitInvert) => {
                    let len = exec_stack.len();
                    if len == 0 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let mut last = &mut exec_stack[len - 1];

                    match last.not() {
                        Some(_) => {}
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::DupAll) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if *memory_size > MEMORY_SIZE / 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::OutOfMemory,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let copy = exec_stack.clone();
                    exec_stack.extend_from_slice(&copy);
                    *memory_size *= 2;
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

                ScriptEntry::Opcode(OP::Hash160ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash160ArrayVar);
                }

                ScriptEntry::Opcode(OP::Hash256ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash256ArrayVar);
                }

                ScriptEntry::Opcode(OP::Hash512ArrayVar) => {
                    self.state =
                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Hash512ArrayVar);
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

                ScriptEntry::Opcode(OP::Min) => {
                    let len = exec_stack.len();
                    if len < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    if !exec_stack[len - 1].is_comparable(&exec_stack[len - 2]) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if exec_stack[len - 1] < exec_stack[len - 2] {
                        let e = exec_stack.remove(len - 2_usize);
                        *memory_size -= e.size();
                    } else {
                        let e = exec_stack.pop().unwrap();
                        *memory_size -= e.size();
                    }
                }

                ScriptEntry::Opcode(OP::Max) => {
                    let len = exec_stack.len();
                    if len < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    if !exec_stack[len - 1].is_comparable(&exec_stack[len - 2]) {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if exec_stack[len - 1] > exec_stack[len - 2] {
                        let e = exec_stack.remove(len - 2_usize);
                        *memory_size -= e.size();
                    } else {
                        let e = exec_stack.pop().unwrap();
                        *memory_size -= e.size();
                    }
                }

                ScriptEntry::Opcode(OP::Within) => {
                    let len = exec_stack.len();
                    if len < 3 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    if !exec_stack[len - 1].is_comparable(&exec_stack[len - 2])
                        || !exec_stack[len - 1].is_comparable(&exec_stack[len - 3])
                    {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let top = exec_stack.pop().unwrap();
                    let left = exec_stack.pop().unwrap();
                    let right = exec_stack.pop().unwrap();

                    *memory_size -= top.size();
                    *memory_size -= left.size();
                    *memory_size -= right.size();

                    if left <= top && top < right {
                        // left-inclusive
                        exec_stack.push(VmTerm::Unsigned8(1));
                        *memory_size += 1;
                    } else {
                        exec_stack.push(VmTerm::Unsigned8(0));
                        *memory_size += 1;
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

                ScriptEntry::Opcode(OP::Add) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    *memory_size -= last.size();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match second.add(&mut last) {
                        Some(_) => {
                            *memory_size += second.size();
                            exec_stack.push(second);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Sub) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    *memory_size -= last.size();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match last.sub(&mut second) {
                        Some(_) => {
                            *memory_size += last.size();
                            exec_stack.push(last);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Mult) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    *memory_size -= last.size();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match second.mul(&mut last) {
                        Some(_) => {
                            *memory_size += second.size();
                            exec_stack.push(second);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Div) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    *memory_size -= last.size();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match last.div(&mut second) {
                        Some(_) => {
                            *memory_size += last.size();
                            exec_stack.push(last);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::BitSHLeft) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match last.sh_left(&mut second) {
                        Some(_) => {
                            exec_stack.push(last);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::BitSHRight) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match last.sh_right(&mut second) {
                        Some(_) => {
                            exec_stack.push(last);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
                    }
                }

                ScriptEntry::Opcode(OP::BitXOR) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.pop().unwrap();
                    let mut second = exec_stack.pop().unwrap();
                    *memory_size -= second.size();

                    match last.xor(&mut second) {
                        Some(_) => {
                            exec_stack.push(last);
                        }
                        None => {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                        }
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

                ScriptEntry::Opcode(OP::TrapIf) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfEq) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfNeq) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfLeq) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfGeq) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfLt) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfGt) => {
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
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::Panic,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::TrapIfNeqType) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::TrapIfNeqType);
                }

                ScriptEntry::Opcode(OP::GhostRider) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let value_to_hash = exec_stack.pop().unwrap();
                    *memory_size -= value_to_hash.size();
                    let new_key = exec_stack.pop().unwrap();
                    *memory_size -= new_key.size();

                    if new_key.get_type() != crate::vm::internal::HASH_KEY_TYPE {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if let VmTerm::Unsigned8Array(arr) = new_key {
                        if arr.len() != 32 {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                            return;
                        }

                        let hash_term =
                            bifs::ghostrider256(&value_to_hash, arr.try_into().unwrap());

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    } else {
                        unreachable!()
                    }
                }

                ScriptEntry::Opcode(OP::Fugue) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::fugue256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::JH256) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::jh256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Ripemd160) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::ripemd160(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Sha256) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::sha256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Sha512) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::sha512(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Keccak256) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::keccak256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Keccak512) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::keccak512(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake2b256) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake2b_256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake2b512) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake2b_512(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake2s256) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake2s_256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_160) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_160(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_256) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_256(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_512) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_512(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_256_160) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_256_160(&val);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_256Keyed) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let value_to_hash = exec_stack.pop().unwrap();
                    *memory_size -= value_to_hash.size();
                    let new_key = exec_stack.pop().unwrap();
                    *memory_size -= new_key.size();

                    if new_key.get_type() != crate::vm::internal::HASH_KEY_TYPE {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if let VmTerm::Unsigned8Array(arr) = new_key {
                        let utf8_key = from_utf8(&arr);
                        if utf8_key.is_err() {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                            return;
                        }

                        let hash_term =
                            bifs::blake3_256_internal(&value_to_hash, utf8_key.unwrap());

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    } else {
                        unreachable!()
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_512Keyed) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let value_to_hash = exec_stack.pop().unwrap();
                    *memory_size -= value_to_hash.size();
                    let new_key = exec_stack.pop().unwrap();
                    *memory_size -= new_key.size();

                    if new_key.get_type() != crate::vm::internal::HASH_KEY_TYPE {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if let VmTerm::Unsigned8Array(arr) = new_key {
                        let utf8_key = from_utf8(&arr);
                        if utf8_key.is_err() {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                            return;
                        }

                        let hash_term =
                            bifs::blake3_512_internal(&value_to_hash, utf8_key.unwrap());

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    } else {
                        unreachable!()
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_160Keyed) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    let value_to_hash = exec_stack.pop().unwrap();
                    *memory_size -= value_to_hash.size();
                    let new_key = exec_stack.pop().unwrap();
                    *memory_size -= new_key.size();

                    if new_key.get_type() != crate::vm::internal::HASH_KEY_TYPE {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                        return;
                    }

                    if let VmTerm::Unsigned8Array(arr) = new_key {
                        let utf8_key = from_utf8(&arr);
                        if utf8_key.is_err() {
                            self.state = ScriptExecutorState::Error(
                                ExecutionResult::InvalidArgs,
                                (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                            );
                            return;
                        }

                        let hash_term =
                            bifs::blake3_160_internal(&value_to_hash, utf8_key.unwrap());

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    } else {
                        unreachable!()
                    }
                }

                ScriptEntry::Opcode(OP::Blake3_160Internal) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_160_internal(&val, key);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_256Internal) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_256_internal(&val, key);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_512Internal) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_512_internal(&val, key);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Blake3_256_160Internal) => match exec_stack.pop() {
                    Some(val) => {
                        *memory_size -= val.size();

                        let hash_term = bifs::blake3_256_160_internal(&val, key);

                        *memory_size += hash_term.size();
                        exec_stack.push(hash_term);
                    }
                    None => {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                },

                ScriptEntry::Opcode(OP::Nop) => {
                    // do nothing
                }

                ScriptEntry::Opcode(_) => {
                    self.state = ScriptExecutorState::Error(
                        ExecutionResult::BadFormat,
                        (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                    );
                }
            },
            _ => unimplemented!(),
        }
    }

    #[inline]
    #[must_use]
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

    /// We hit an OP_ReturnFunc
    ReturnFunc,

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
        if let ScriptEntry::Byte(len) = &self.script[0] {
            debug_assert_eq!(*len as usize, self.malleable_args.len());
            // Encode script length + bitmaps length
            bincode::Encode::encode(&(self.script.len() + (*len >> 3) as usize + 1), encoder)?;
            // Encode args length
            bincode::Encode::encode(len, encoder)?;
        } else {
            unreachable!();
        }

        // Encode bitmaps
        for chunk in self.malleable_args.chunks(8) {
            let mut bitmap: u8 = 0x00;
            for (i, val) in chunk.iter().enumerate() {
                let v = u8::from(*val);
                bitmap = set_bit!(bitmap, i as u8, v);
            }
            bincode::Encode::encode(&bitmap, encoder)?;
        }

        // Encode script
        for e in &self.script[1..] {
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
        let len: u16 = bincode::Decode::decode(decoder)?;
        let len = len as usize;
        let mut script_parser = ScriptParser::new(len);

        for _ in 0..len {
            let byte: u8 = bincode::Decode::decode(decoder)?;

            script_parser
                .push_byte(byte)
                .map_err(|err| bincode::error::DecodeError::OtherString(err.to_owned()))?;
        }

        let (script, malleable_args, functions) = script_parser.out();

        Ok(Self {
            script,
            functions,
            malleable_args,
        })
    }
}

struct ScriptParser {
    state: ScriptParserState,
    out: Vec<ScriptEntry>,
    malleable_args: BitVec,
    current_func: Option<Vec<ScriptEntry>>,
    functions: Vec<Vec<ScriptEntry>>,
}

macro_rules! push_out {
    ($self:expr, $entry:expr) => {{
        if let Some(ref mut func) = &mut $self.current_func {
            func.push($entry);
        } else {
            $self.out.push($entry);
        }
    }};
}

macro_rules! impl_parser_expecting_bytes {
    ($self:expr, $op:expr, $len:expr) => {{
        push_out!($self, ScriptEntry::Opcode($op));

        match &$self.state {
            ScriptParserState::ExpectingOP => {
                $self.state = ScriptParserState::ExpectingBytes($len, None, true);
            }

            ScriptParserState::ExpectingOPButNotFuncOrEnd => {
                $self.state = ScriptParserState::ExpectingBytes($len, None, false);
            }

            ScriptParserState::ExpectingOPCF(cf_stack, blocks_allowed) => {
                $self.state = ScriptParserState::ExpectingBytes(
                    $len,
                    Some(cf_stack.clone()),
                    *blocks_allowed,
                );
            }

            _ => unreachable!(),
        }

        Ok(())
    }};
}

macro_rules! impl_parser_expecting_len {
    ($self:expr, $op:expr) => {{
        push_out!($self, ScriptEntry::Opcode($op));

        match &$self.state {
            ScriptParserState::ExpectingOP => {
                $self.state = ScriptParserState::ExpectingLen($op, 0, 0, None, true);
            }

            ScriptParserState::ExpectingOPButNotFuncOrEnd => {
                $self.state = ScriptParserState::ExpectingLen($op, 0, 0, None, false);
            }

            ScriptParserState::ExpectingOPCF(cf_stack, blocks_allowed) => {
                $self.state = ScriptParserState::ExpectingLen(
                    $op,
                    0,
                    0,
                    Some(cf_stack.clone()),
                    *blocks_allowed,
                );
            }

            _ => unreachable!(),
        }

        Ok(())
    }};
}

impl ScriptParser {
    pub fn new(len: usize) -> Self {
        Self {
            state: ScriptParserState::ExpectingArgsLen,
            out: Vec::with_capacity(len),
            malleable_args: bitvec_from_bools![],
            current_func: None,
            functions: vec![],
        }
    }

    fn _out(&mut self) -> &mut Vec<ScriptEntry> {
        if let Some(ref mut func) = &mut self.current_func {
            func
        } else {
            &mut self.out
        }
    }

    pub fn push_byte(&mut self, byte: u8) -> Result<(), &'static str> {
        match &mut self.state {
            ScriptParserState::ExpectingArgsLen => {
                self.out.push(ScriptEntry::Byte(byte));
                if byte == 0x00 {
                    self.state = ScriptParserState::ExpectingOPButNotFuncOrEnd;
                    Ok(())
                } else {
                    let bitmaps = (byte >> 3) + 1;
                    self.state = ScriptParserState::ExpectingScriptFlags(
                        bitmaps,
                        byte,
                        BitVec::with_capacity(bitmaps as usize),
                    );
                    Ok(())
                }
            }

            ScriptParserState::ExpectingFuncArgsLen => {
                push_out!(self, ScriptEntry::Byte(byte));
                self.state = ScriptParserState::ExpectingOP;
                Ok(())
            }

            ScriptParserState::ExpectingScriptFlags(
                ref mut bitmaps,
                total,
                ref mut malleable_args,
            ) if bitmaps > &mut 1 => {
                malleable_args.push(check_bit!(byte, 0));
                malleable_args.push(check_bit!(byte, 1));
                malleable_args.push(check_bit!(byte, 2));
                malleable_args.push(check_bit!(byte, 3));
                malleable_args.push(check_bit!(byte, 4));
                malleable_args.push(check_bit!(byte, 5));
                malleable_args.push(check_bit!(byte, 6));
                malleable_args.push(check_bit!(byte, 7));
                *bitmaps -= 1;
                Ok(())
            }

            ScriptParserState::ExpectingScriptFlags(bitmaps, total, ref mut malleable_args)
                if bitmaps == &1 =>
            {
                let m = *total % 8;
                for i in 0..m {
                    malleable_args.push(check_bit!(byte, i));
                }
                self.malleable_args = malleable_args.clone();
                self.state = ScriptParserState::ExpectingOPButNotFuncOrEnd;
                Ok(())
            }

            ScriptParserState::ExpectingScriptFlags(_, _, _) => {
                unreachable!()
            }

            ScriptParserState::ExpectingOP
            | ScriptParserState::ExpectingOPButNotFuncOrEnd
            | ScriptParserState::ExpectingOPCF(_, _) => match OP::from_u8(byte) {
                Some(OP::Unsigned8Var) => impl_parser_expecting_bytes!(self, OP::Unsigned8Var, 1),
                Some(OP::Signed8Var) => impl_parser_expecting_bytes!(self, OP::Unsigned8Var, 1),
                Some(OP::Unsigned16Var) => impl_parser_expecting_bytes!(self, OP::Unsigned16Var, 2),
                Some(OP::Signed16Var) => impl_parser_expecting_bytes!(self, OP::Unsigned16Var, 2),
                Some(OP::Unsigned32Var) => impl_parser_expecting_bytes!(self, OP::Unsigned32Var, 4),
                Some(OP::Signed32Var) => impl_parser_expecting_bytes!(self, OP::Unsigned32Var, 4),
                Some(OP::Unsigned64Var) => impl_parser_expecting_bytes!(self, OP::Unsigned64Var, 8),
                Some(OP::Signed64Var) => impl_parser_expecting_bytes!(self, OP::Unsigned64Var, 8),
                Some(OP::Unsigned128Var) => {
                    impl_parser_expecting_bytes!(self, OP::Unsigned128Var, 16)
                }
                Some(OP::Signed128Var) => {
                    impl_parser_expecting_bytes!(self, OP::Unsigned128Var, 16)
                }
                Some(OP::UnsignedBigVar) => {
                    impl_parser_expecting_bytes!(self, OP::UnsignedBigVar, 32)
                }
                Some(OP::SignedBigVar) => impl_parser_expecting_bytes!(self, OP::SignedBigVar, 32),
                Some(OP::Hash160Var) => impl_parser_expecting_bytes!(self, OP::Hash160Var, 20),
                Some(OP::Hash256Var) => impl_parser_expecting_bytes!(self, OP::Hash256Var, 32),
                Some(OP::Hash512Var) => impl_parser_expecting_bytes!(self, OP::Hash512Var, 64),
                Some(OP::Pick) => impl_parser_expecting_bytes!(self, OP::Pick, 1),
                Some(OP::Hash160ArrayVar) => impl_parser_expecting_len!(self, OP::Hash160ArrayVar),
                Some(OP::Hash256ArrayVar) => impl_parser_expecting_len!(self, OP::Hash256ArrayVar),
                Some(OP::Hash512ArrayVar) => impl_parser_expecting_len!(self, OP::Hash512ArrayVar),
                Some(OP::Unsigned8ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Unsigned8ArrayVar)
                }
                Some(OP::Signed8ArrayVar) => impl_parser_expecting_len!(self, OP::Signed8ArrayVar),
                Some(OP::Unsigned16ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Unsigned16ArrayVar)
                }
                Some(OP::Signed16ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Signed16ArrayVar)
                }
                Some(OP::Unsigned32ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Unsigned32ArrayVar)
                }
                Some(OP::Signed32ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Signed32ArrayVar)
                }
                Some(OP::Unsigned64ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Unsigned64ArrayVar)
                }
                Some(OP::Signed64ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Signed64ArrayVar)
                }
                Some(OP::Unsigned128ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Unsigned128ArrayVar)
                }
                Some(OP::Signed128ArrayVar) => {
                    impl_parser_expecting_len!(self, OP::Signed128ArrayVar)
                }
                Some(OP::UnsignedBigArrayVar) => {
                    impl_parser_expecting_len!(self, OP::UnsignedBigArrayVar)
                }
                Some(OP::SignedBigArrayVar) => {
                    impl_parser_expecting_len!(self, OP::SignedBigArrayVar)
                }
                Some(OP::Substr) => impl_parser_expecting_bytes!(self, OP::Substr, 2),
                Some(OP::TrapIfNeqType) => impl_parser_expecting_bytes!(self, OP::TrapIfNeqType, 1),
                Some(OP::Func | OP::End)
                    if matches!(self.state, ScriptParserState::ExpectingOPButNotFuncOrEnd) =>
                {
                    Err("did not expect a func or end opcode")
                }
                Some(OP::Func) if matches!(self.state, ScriptParserState::ExpectingOP) => {
                    if self.current_func.is_some() {
                        return Err("invalid function declaration, did not expect an OP_Func");
                    }
                    self.current_func = Some(vec![]);
                    self.state = ScriptParserState::ExpectingFuncArgsLen;
                    Ok(())
                }
                Some(OP::End) if matches!(self.state, ScriptParserState::ExpectingOP) => {
                    if self.current_func.is_none() {
                        return Err("invalid function declaration, did not expect an OP_End");
                    }
                    let func = self.current_func.take().unwrap();
                    self.functions.push(func);
                    Ok(())
                }
                Some(OP::End) if !matches!(self.state, ScriptParserState::ExpectingOPCF(_, _)) => {
                    Err("invalid script, did not expect an end opcode")
                }
                Some(OP::End) if matches!(self.state, ScriptParserState::ExpectingOPCF(_, _)) => {
                    push_out!(self, ScriptEntry::Opcode(OP::End));
                    let mut empty_cf_stack = false;
                    let mut ba = false;
                    if let ScriptParserState::ExpectingOPCF(ref mut cf_stack, blocks_allowed) =
                        self.state
                    {
                        cf_stack.pop();
                        if cf_stack.is_empty() {
                            empty_cf_stack = true;
                            ba = blocks_allowed;
                        }
                    } else {
                        unreachable!();
                    }
                    if empty_cf_stack {
                        if ba {
                            self.state = ScriptParserState::ExpectingOP;
                        } else {
                            self.state = ScriptParserState::ExpectingOPButNotFuncOrEnd;
                        }
                    }
                    Ok(())
                }
                Some(OP::Loop) if matches!(self.state, ScriptParserState::ExpectingOP) => {
                    push_out!(self, ScriptEntry::Opcode(OP::Loop));
                    self.state = ScriptParserState::ExpectingOPCF(vec![OP::Loop], true);
                    Ok(())
                }
                Some(OP::Loop)
                    if matches!(self.state, ScriptParserState::ExpectingOPButNotFuncOrEnd) =>
                {
                    push_out!(self, ScriptEntry::Opcode(OP::Loop));
                    self.state = ScriptParserState::ExpectingOPCF(vec![OP::Loop], false);
                    Ok(())
                }
                Some(OP::Loop) if matches!(self.state, ScriptParserState::ExpectingOPCF(_, _)) => {
                    push_out!(self, ScriptEntry::Opcode(OP::Loop));
                    if let ScriptParserState::ExpectingOPCF(ref mut cf_stack, _) = self.state {
                        cf_stack.push(OP::Loop);
                    } else {
                        unreachable!();
                    }
                    Ok(())
                }
                Some(OP::Call) => {
                    push_out!(self, ScriptEntry::Opcode(OP::Call));

                    match &self.state {
                        ScriptParserState::ExpectingOPButNotFuncOrEnd => {
                            self.state = ScriptParserState::ExpectingBytes(1, None, true);
                        }
                        ScriptParserState::ExpectingOPCF(cf_stack, allows_funcs)
                            if !*allows_funcs =>
                        {
                            self.state =
                                ScriptParserState::ExpectingBytes(1, Some(cf_stack.clone()), true);
                        }
                        _ => {} // Do nothing
                    }

                    Ok(())
                }
                Some(op) => {
                    push_out!(self, ScriptEntry::Opcode(op));
                    Ok(())
                }
                None => Err("invalid op"),
            },

            ScriptParserState::ExpectingBytes(ref mut i, cf_stack, blocks_allowed) => {
                push_out!(self, ScriptEntry::Byte(byte));
                *i -= 1;

                if *i == 0 {
                    match cf_stack {
                        Some(cf_stack) => {
                            self.state =
                                ScriptParserState::ExpectingOPCF(cf_stack.clone(), *blocks_allowed);
                        }
                        None => {
                            if *blocks_allowed {
                                self.state = ScriptParserState::ExpectingOP;
                            } else {
                                self.state = ScriptParserState::ExpectingOPButNotFuncOrEnd;
                            }
                        }
                    }
                }

                Ok(())
            }

            ScriptParserState::ExpectingLen(
                op,
                ref mut sum,
                ref mut i,
                cf_stack,
                blocks_allowed,
            ) => {
                push_out!(self, ScriptEntry::Byte(byte));
                let b = u16::from(byte);
                if *i == 0 {
                    *sum += b;
                } else {
                    *sum += b << 8;
                }
                *i += 1;

                if *i == 2 {
                    match op {
                        OP::Hash160ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 20) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Hash256ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 32) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Hash512ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 64) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Unsigned8ArrayVar | OP::Signed8ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Unsigned16ArrayVar | OP::Signed16ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 2) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Unsigned32ArrayVar | OP::Signed32ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 4) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Unsigned64ArrayVar | OP::Signed64ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 8) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::Unsigned128ArrayVar | OP::Signed128ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 16) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
                            Ok(())
                        }
                        OP::UnsignedBigArrayVar | OP::SignedBigArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes(
                                (*sum * 32) as usize,
                                cf_stack.clone(),
                                *blocks_allowed,
                            );
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

    pub fn out(self) -> (Vec<ScriptEntry>, BitVec, Vec<Vec<ScriptEntry>>) {
        (self.out, self.malleable_args, self.functions)
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
    pub(crate) func_idx: Option<usize>,
    pub(crate) i_ptr: usize,
    pub(crate) entry: ScriptEntry,
}

impl From<(usize, Option<usize>, ScriptEntry, &[VmTerm])> for StackTrace {
    fn from(
        (i_ptr, func_idx, entry, top_frame_stack): (usize, Option<usize>, ScriptEntry, &[VmTerm]),
    ) -> Self {
        let ti = TraceItem {
            func_idx,
            i_ptr,
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

impl From<(usize, Option<usize>, OP, &[VmTerm])> for StackTrace {
    fn from(
        (i_ptr, func_idx, entry, top_frame_stack): (usize, Option<usize>, OP, &[VmTerm]),
    ) -> Self {
        (i_ptr, func_idx, ScriptEntry::Opcode(entry), top_frame_stack).into()
    }
}

impl From<(usize, Option<usize>, OP)> for TraceItem {
    fn from((i_ptr, func_idx, entry): (usize, Option<usize>, OP)) -> Self {
        (i_ptr, func_idx, ScriptEntry::Opcode(entry)).into()
    }
}

impl From<(usize, Option<usize>, ScriptEntry)> for TraceItem {
    fn from((i_ptr, func_idx, entry): (usize, Option<usize>, ScriptEntry)) -> Self {
        Self {
            func_idx,
            i_ptr,
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
    #[must_use]
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }

    #[must_use]
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
    /// Expecting main function arguments length
    ExpectingArgsLen,

    /// Expecting function arguments length
    ExpectingFuncArgsLen,

    /// Expecting script flags. The state tuple is (remaining_bitmaps, args_len, bitmaps_vec)
    ExpectingScriptFlags(u8, u8, BitVec),

    /// Expecting any OP
    ExpectingOP,

    /// Expecting any OP except OP_Func or OP_End
    ExpectingOPButNotFuncOrEnd,

    /// Expecting any OP while also tracking the Control Flow
    ExpectingOPCF(Vec<OP>, bool),

    /// Expecting n bytes. The state tuple is (num_bytes, cf_stack, funcs_allowed)
    ExpectingBytes(usize, Option<Vec<OP>>, bool),

    /// Expecting length for for OP
    ExpectingLen(OP, u16, usize, Option<Vec<OP>>, bool),
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

    fn assert_script_ok(mut script: Script, outputs: Vec<VmTerm>, key: &str) {
        script.populate_malleable_args_field();
        let base: TestBaseArgs = get_test_base_args(&mut script, 30, outputs, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];
        assert_eq!(
            script.execute(
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

    fn assert_script_fail(
        mut script: Script,
        outputs: Vec<VmTerm>,
        key: &str,
        exec_res: ExecutionResult,
    ) {
        script.populate_malleable_args_field();
        let base: TestBaseArgs = get_test_base_args(&mut script, 30, outputs, 0, key);
        let mut idx_map = HashMap::new();
        let mut outs = vec![];
        assert_eq!(
            script.execute(
                &base.args,
                &base.ins,
                &mut outs,
                &mut idx_map,
                [0; 32],
                key,
                VmFlags::default()
            ),
            Err((exec_res, StackTrace::default())).into()
        );
    }

    fn get_test_base_args(
        ss: &mut Script,
        out_amount: Money,
        out_script: Vec<VmTerm>,
        push_out_cycles: usize,
        key: &str,
    ) -> TestBaseArgs {
        ss.populate_malleable_args_field();
        let sh = ss.to_script_hash(key);
        let args = vec![
            VmTerm::Signed128(30),
            VmTerm::Hash160([0; 20]),
            VmTerm::Hash160(sh.0),
        ];
        let mut ins = vec![Input {
            out: None,
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
    fn it_parses_script_with_only_main() {
        let script: Vec<u8> = vec![
            0x17, // Script length
            0x03, // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            0x00, // Script flags
            0x23, // OP_Unsigned8Var,
            0x00, // Push 0 to the stack
            0x57, // OP_Loop
            0x57, // OP_Loop
            0x58, // OP_Break
            0xb6, // OP_End
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0xcf, // OP_PushOut,
            0x82, // OP_Add1,
            0x70, // OP_Pick,
            0x00, // Pick at index 0
            0x23, // OP_Unsigned8Var,
            0x03, // Push 3 to the stack
            0x5b, // OP_BreakIfEq
            0xb6, // OP_End
            0xb7, // OP_Verify
        ];

        let oracle_script = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Break),
                ScriptEntry::Opcode(OP::End),
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
            malleable_args: bitvec_from_bools![false, false, false],
            ..Script::default()
        };

        let decoded: Script = crate::codec::decode(&script).unwrap();

        assert_eq!(decoded, oracle_script);
    }

    #[test]
    fn it_fails_to_parse_script_with_duplicate_end_opcodes() {
        let script: Vec<u8> = vec![
            0x15, // Script length
            0x03, // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            0x00, // Script flags
            0x23, // OP_Unsigned8Var,
            0x00, // Push 0 to the stack
            0x57, // OP_Loop
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0xcf, // OP_PushOut,
            0x82, // OP_Add1,
            0x70, // OP_Pick,
            0x00, // Pick at index 0
            0x23, // OP_Unsigned8Var,
            0x03, // Push 3 to the stack
            0x5b, // OP_BreakIfEq
            0xb6, // OP_End
            0xb6, // OP_End
            0xb7, // OP_Verify
        ];

        assert!(crate::codec::decode::<Script>(&script).is_err());
    }

    #[test]
    fn it_fails_to_parse_script_with_invalid_end_opcodes() {
        let script: Vec<u8> = vec![
            0x13, // Script length
            0x03, // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            0x00, // Script flags
            0x23, // OP_Unsigned8Var,
            0x00, // Push 0 to the stack
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0xcf, // OP_PushOut,
            0x82, // OP_Add1,
            0x70, // OP_Pick,
            0x00, // Pick at index 0
            0x23, // OP_Unsigned8Var,
            0x03, // Push 3 to the stack
            0x5b, // OP_BreakIfEq
            0xb6, // OP_End
            0xb7, // OP_Verify
        ];

        assert!(crate::codec::decode::<Script>(&script).is_err());
    }

    #[test]
    fn it_fails_to_parse_script_with_more_script_flags_than_necessary() {
        let script: Vec<u8> = vec![
            0x15, // Script length
            0x03, // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            0x00, // Script flags
            0x00, // Script flags
            0x23, // OP_Unsigned8Var,
            0x00, // Push 0 to the stack
            0x57, // OP_Loop
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0x70, // OP_Pick,
            0x03, // Pick at index 3
            0xcf, // OP_PushOut,
            0x82, // OP_Add1,
            0x70, // OP_Pick,
            0x00, // Pick at index 0
            0x23, // OP_Unsigned8Var,
            0x03, // Push 3 to the stack
            0x5b, // OP_BreakIfEq
            0xb6, // OP_End
            0xb7, // OP_Verify
        ];

        assert!(crate::codec::decode::<Script>(&script).is_err());
    }

    #[test]
    fn it_parses_script_with_multiple_functions() {
        let script: Vec<u8> = vec![
            0x13, // Script length
            0x03, // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
            0x00, // Script flags
            0x23, // OP_Unsigned8Var,
            0x00, // Push 0 to the stack
            0x57, // OP_Loop
            0xaf, // OP_Call
            0x00, // Call function with index 0
            0x70, // OP_Pick,
            0x00, // Pick at index 0
            0x23, // OP_Unsigned8Var,
            0x03, // Push 3 to the stack
            0x5b, // OP_BreakIfEq
            0xb6, // OP_End
            0xb7, // OP_Verify
            0x00, // OP_Func
            0x01, // 1 argument pushed onto the stack
            0x82, // OP_Add1,
            0xb8, // OP_ReturnFunc,
            0xb6, // OP_End
        ];

        let oracle_script = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Call),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfEq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
            malleable_args: bitvec_from_bools![false, false, false],
            functions: vec![vec![
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::ReturnFunc),
            ]],
        };

        let decoded: Script = crate::codec::decode(&script).unwrap();
        assert_eq!(decoded, oracle_script);
    }

    #[test]
    fn set_bit() {
        assert_eq!(set_bit!(0_u8, 0_u8, 1_u8), 0b0000_0001);
    }

    #[test]
    fn check_bit() {
        assert!(check_bit!(0b0000_0001, 0));
        assert!(!check_bit!(0b0000_0000, 0));
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
        let mut ss = Script {
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
            ..Script::default()
        };
        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
    fn it_calls_function() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Loop),
                ScriptEntry::Opcode(OP::Call),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Pick),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::BreakIfEq),
                ScriptEntry::Opcode(OP::End),
                ScriptEntry::Opcode(OP::Verify),
            ],
            malleable_args: bitvec_from_bools![false, false, false],
            functions: vec![vec![
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Add1),
                ScriptEntry::Opcode(OP::ReturnFunc),
            ]],
        };
        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
    }

    #[test]
    fn it_breaks_loop_if_values_not_equal() {
        let key = "test_key";
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 60, vec![], 1, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 60, vec![], 1, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 60, vec![], 1, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 90, vec![], 2, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 60, vec![], 1, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 120, vec![], 3, key);
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
            malleable_args: bitvec_from_bools![false, false, false],
            ..Script::default()
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
            malleable_args: bitvec_from_bools![false],
            ..Script::default()
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        assert_eq!(
            encoded,
            vec![0x0a, 0x01, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00, 0x24, 0x00, 0x00]
        );
    }

    #[test]
    fn it_encodes_to_single_byte_2() {
        let script = Script {
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
            malleable_args: bitvec_from_bools![false],
            ..Script::default()
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        assert_eq!(
            encoded,
            vec![0x0a, 0x01, 0x00, 0x25, 0xff, 0xff, 0xff, 0xff, 0x24, 0xff, 0xff]
        );
    }

    #[test]
    fn it_encodes_and_decodes() {
        let script = Script {
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
            malleable_args: bitvec_from_bools![false],
            ..Script::default()
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
            malleable_args: bitvec_from_bools![false],
            ..Script::default()
        };
        let encoded = crate::codec::encode_to_vec(&script).unwrap();
        let decoded: Script = crate::codec::decode(&encoded).unwrap();
        assert_eq!(decoded, script);
    }

    #[test]
    fn it_roll_pop_out() {
        let key = "test_key";
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(7),
            VmTerm::Unsigned16(6),
            VmTerm::Unsigned16(5),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(7),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_dup_all() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0xaa),
                ScriptEntry::Byte(0xbb),
                ScriptEntry::Byte(0xcc),
                ScriptEntry::Byte(0xdd),
                ScriptEntry::Opcode(OP::DupAll),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(0xddcc_bbaa),
            VmTerm::Unsigned8(0x03),
            VmTerm::Unsigned8(0x02),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned32(0xddcc_bbaa),
            VmTerm::Unsigned8(0x03),
            VmTerm::Unsigned8(0x02),
            VmTerm::Unsigned8(0x01),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8(4), VmTerm::Unsigned8(1)];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(5),
            VmTerm::Unsigned8(4),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(0),
            VmTerm::Unsigned8(5),
            VmTerm::Unsigned8(4),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(5),
            VmTerm::Unsigned8(4),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(3),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8(5)];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
            VmTerm::Unsigned8(2),
            VmTerm::Unsigned8(1),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
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
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![VmTerm::Unsigned64(1), VmTerm::Unsigned8(0)];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Drop),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Nip),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Over),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Swap),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Tuck),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Drop2),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Dup2),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Size),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, vec![], 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
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
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
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
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
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
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x11),
            VmTerm::Unsigned8(0x23),
            VmTerm::Unsigned8(0x01),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(0x0011),
            VmTerm::Unsigned16(0x2301),
            VmTerm::Unsigned16(0x0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(0x0000_0011),
            VmTerm::Unsigned32(0x0000_2301),
            VmTerm::Unsigned32(0x0000_0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned64(0x0000_0000_0000_0011),
            VmTerm::Unsigned64(0x0123_0000_0000_2301),
            VmTerm::Unsigned64(0x0123_0000_0000_0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned128(0x2200_0000_0000_0000_0123_0000_0000_2301),
            VmTerm::Unsigned128(0x1100_0000_0000_0000_0123_0000_0000_0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed16(0x0011),
            VmTerm::Signed16(0x2301),
            VmTerm::Signed16(0x0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed32(0x0000_0011),
            VmTerm::Signed32(0x0000_2301),
            VmTerm::Signed32(0x0000_0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed64(0x0000_0000_0000_0011),
            VmTerm::Signed64(0x0123_0000_0000_2301),
            VmTerm::Signed64(0x0123_0000_0000_0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed128(0x2200_0000_0000_0000_0123_0000_0000_2301),
            VmTerm::Signed128(0x1100_0000_0000_0000_0123_0000_0000_0123),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_loads_hash_160_array_var() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Hash160ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
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
                ScriptEntry::Byte(0x85),
                ScriptEntry::Byte(0x36),
                ScriptEntry::Byte(0x69),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Byte(0x22),
                ScriptEntry::Byte(0x35),
                ScriptEntry::Byte(0x78),
                ScriptEntry::Byte(0x57),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Hash160ArrayVar),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
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
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash160Array(vec![
                [
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85,
                    0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
                ],
                [
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85,
                    0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
                ],
            ]),
            VmTerm::Hash160Array(vec![[
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
            ]]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_loads_hash_256_array_var() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Hash256ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
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
                ScriptEntry::Opcode(OP::Hash256ArrayVar),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
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
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash256Array(vec![
                [
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85,
                    0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53,
                    0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
                ],
                [
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85,
                    0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53,
                    0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
                ],
            ]),
            VmTerm::Hash256Array(vec![[
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47,
                0x35, 0x12, 0x18, 0x34,
            ]]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_loads_hash_512_array_var() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Hash512ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
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
                ScriptEntry::Opcode(OP::Hash512ArrayVar),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
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
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash512Array(vec![
                [
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85,
                    0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53,
                    0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23,
                    0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
                ],
                [
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85,
                    0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53,
                    0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23,
                    0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57,
                    0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
                ],
            ]),
            VmTerm::Hash512Array(vec![[
                0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34, 0x85, 0x36,
                0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47,
                0x35, 0x12, 0x18, 0x34, 0x36, 0x23, 0x74, 0x23, 0x78, 0x53, 0x23, 0x47, 0x35, 0x12,
                0x18, 0x34, 0x85, 0x36, 0x69, 0x09, 0x22, 0x35, 0x78, 0x57, 0x36, 0x23, 0x74, 0x23,
                0x78, 0x53, 0x23, 0x47, 0x35, 0x12, 0x18, 0x34,
            ]]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x3f, 0x79, 0x25, 0xae, 0x77, 0xa1]),
            VmTerm::Unsigned8Array(vec![0x75, 0xaf, 0xf6, 0xa5]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16Array(vec![0x3ffe, 0x7926, 0x2510, 0xaebc, 0x7727, 0xa123]),
            VmTerm::Unsigned16Array(vec![0x7536, 0x7516, 0xaf41, 0xa5f6]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32Array(vec![
                0xa5f6_af41,
                0x7516_7536,
                0x7516_7536,
                0x7516_7536,
                0x7516_7536,
                0xa5f6_af41,
            ]),
            VmTerm::Unsigned32Array(vec![0x01fe_7814, 0x7516_7536, 0xa5f6_af41, 0x7516_7536]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned64Array(vec![
                0xa5f6_af41_a5f6_af41,
                0x7516_7536_7516_7536,
                0x7516_7536_7516_7536,
                0x7516_7536_7516_7536,
                0x7516_7536_7516_7536,
                0xa5f6_af41_a5f6_af41,
            ]),
            VmTerm::Unsigned64Array(vec![
                0x01fe_7814_01fe_7814,
                0x7516_7536_7516_7536,
                0xa5f6_af41_a5f6_af41,
                0x7516_7536_7516_7536,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned128Array(vec![
                0x7516_7536_7516_7536_a5f6_af41_a5f6_af41,
                0x7516_7536_7516_7536_7516_7536_7516_7536,
                0xa5f6_af41_a5f6_af41_7516_7536_7516_7536,
            ]),
            VmTerm::Unsigned128Array(vec![
                0x7516_7536_7516_7536_01fe_7814_01fe_7814,
                0x7516_7536_7516_7536_a5f6_af41_a5f6_af41,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed8Array(vec![0x3f, 0x79, 0x25, 0x12, 0x77, 0x11]),
            VmTerm::Signed8Array(vec![0x75, 0x12, 0x34, 0x54]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed16Array(vec![0x3ffe, 0x7926, 0x2510, 0x2ebc, 0x7727, 0x1123]),
            VmTerm::Signed16Array(vec![0x7536, 0x7516, 0x1f41, 0x15f6]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed32Array(vec![
                0x15f6_af41,
                0x7516_7536,
                0x7516_7536,
                0x7516_7536,
                0x7516_7536,
                0x15f6_af41,
            ]),
            VmTerm::Signed32Array(vec![0x01fe_7814, 0x7516_7536, 0x15f6_af41, 0x7516_7536]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed64Array(vec![
                0x15f6_af41_a5f6_af41,
                0x7516_7536_7516_7536,
                0x7516_7536_7516_7536,
                0x7516_7536_7516_7536,
                0x7516_7536_7516_7536,
                0x15f6_af41_a5f6_af41,
            ]),
            VmTerm::Signed64Array(vec![
                0x01fe_7814_01fe_7814,
                0x7516_7536_7516_7536,
                0x15f6_af41_a5f6_af41,
                0x7516_7536_7516_7536,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed128Array(vec![
                0x7516_7536_7516_7536_a5f6_af41_a5f6_af41,
                0x7516_7536_7516_7536_7516_7536_7516_7536,
                0x15f6_af41_a5f6_af41_7516_7536_7516_7536,
            ]),
            VmTerm::Signed128Array(vec![
                0x7516_7536_7516_7536_01fe_7814_01fe_7814,
                0x7516_7536_7516_7536_a5f6_af41_a5f6_af41,
            ]),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned16(0x0004), VmTerm::Unsigned16(0x0006)];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
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
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash160Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomHash160Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash160(rng.gen::<[u8; 20]>()),
            VmTerm::Hash160(rng.gen::<[u8; 20]>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash256Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomHash256Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Hash256(rng.gen::<[u8; 32]>()),
            VmTerm::Hash256(rng.gen::<[u8; 32]>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomHash512Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomHash512Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
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
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(rng.gen::<u8>()),
            VmTerm::Unsigned8(rng.gen::<u8>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned16(rng.gen::<u16>()),
            VmTerm::Unsigned16(rng.gen::<u16>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(rng.gen::<u32>()),
            VmTerm::Unsigned32(rng.gen::<u32>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned64(rng.gen::<u64>()),
            VmTerm::Unsigned64(rng.gen::<u64>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomUnsigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomUnsigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned128(rng.gen::<u128>()),
            VmTerm::Unsigned128(rng.gen::<u128>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned8Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed8(rng.gen::<i8>()),
            VmTerm::Signed8(rng.gen::<i8>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned16Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed16(rng.gen::<i16>()),
            VmTerm::Signed16(rng.gen::<i16>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned32Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed32(rng.gen::<i32>()),
            VmTerm::Signed32(rng.gen::<i32>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned64Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed64(rng.gen::<i64>()),
            VmTerm::Signed64(rng.gen::<i64>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::RandomSigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::RandomSigned128Var),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Signed128(rng.gen::<i128>()),
            VmTerm::Signed128(rng.gen::<i128>()),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
            ..Script::default()
        };

        let script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x00),
            VmTerm::Unsigned8(0x00),
        ];
        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_ghostrider() {
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
                ScriptEntry::Opcode(OP::Signed8Var), // Value
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::GhostRider),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];
        let new_key: [u8; 32] = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
            0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
            0x1d, 0x1e, 0x1f, 0x2a,
        ];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::ghostrider256(&term, new_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_fails_ghostrider_hashing_with_wrong_key_type() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar), // Key
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::GhostRider),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_fails_ghostrider_hashing_with_wrong_key_length() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x1f),
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
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::GhostRider),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_hashes_with_fugue() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Fugue),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x10),
                ScriptEntry::Opcode(OP::Fugue),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::Fugue),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xc1),
                ScriptEntry::Opcode(OP::Fugue),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Opcode(OP::Fugue),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Unsigned8(0x10),
            VmTerm::Unsigned8(0xa5),
            VmTerm::Unsigned8(0xc1),
            VmTerm::Unsigned8(0xff),
        ];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::fugue256(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_jh256() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::JH256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::JH256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::jh256(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::ripemd160(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::sha256(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::sha512(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
        let mut ss = Script {
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
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in &test_terms {
            let hashed_term_256 = bifs::blake2b_256(term);
            script_output.push(hashed_term_256);
        }
        for term in &test_terms {
            let hashed_term_512 = bifs::blake2b_512(term);
            script_output.push(hashed_term_512);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_160() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_160),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_160),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_160(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_256() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_256(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_512() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_512),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_512),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_512(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_256_160() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_256_160),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_256_160),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_256_160(&term);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_256_keyed() {
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
                ScriptEntry::Opcode(OP::Signed8Var), // Value
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_256Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];
        let utf_key = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a];
        let utf_key = from_utf8(&utf_key.as_slice()).unwrap();

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_256_internal(&term, &utf_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_256_keyed_with_valid_utf8_key() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Byte(0x8f),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_256Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01)];
        let utf_key = vec![0xe2, 0x9d, 0xa4, 0xef, 0xb8, 0x8f];
        let utf_key = from_utf8(&utf_key.as_slice()).unwrap();

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_256_internal(&term, &utf_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_panics_hashing_with_blake3_256_keyed_because_of_invalid_key_type() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar), // Key
                ScriptEntry::Byte(0x05),
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
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_panics_hashing_with_blake3_256_keyed_with_invalid_utf8_key() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_256Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_hashes_with_blake3_512_keyed() {
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
                ScriptEntry::Opcode(OP::Signed8Var), // Value
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_512Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];
        let utf_key = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a];
        let utf_key = from_utf8(&utf_key.as_slice()).unwrap();

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_512_internal(&term, &utf_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_512_keyed_with_valid_utf8_key() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Byte(0x8f),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_512Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Byte(0x8f),
                ScriptEntry::Opcode(OP::Signed8Var), // Value
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_512Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];
        let utf_key = vec![0xe2, 0x9d, 0xa4, 0xef, 0xb8, 0x8f];
        let utf_key = from_utf8(&utf_key.as_slice()).unwrap();

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_512_internal(&term, &utf_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_panics_hashing_with_blake3_512_keyed_because_of_invalid_key_type() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar), // Key
                ScriptEntry::Byte(0x05),
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
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_panics_hashing_with_blake3_512_keyed_with_invalid_utf8_key() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_512Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_hashes_with_blake3_160_keyed() {
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
                ScriptEntry::Opcode(OP::Signed8Var), // Value
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_160Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];
        let utf_key = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a];
        let utf_key = from_utf8(&utf_key.as_slice()).unwrap();

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_160_internal(&term, &utf_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_160_keyed_with_valid_utf8_key() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Byte(0x8f),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_160Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x06),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Byte(0x8f),
                ScriptEntry::Opcode(OP::Signed8Var), // Value
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_160Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];
        let utf_key = vec![0xe2, 0x9d, 0xa4, 0xef, 0xb8, 0x8f];
        let utf_key = from_utf8(&utf_key.as_slice()).unwrap();

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_160_internal(&term, &utf_key);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_panics_hashing_with_blake3_160_keyed_because_of_invalid_key_type() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar), // Key
                ScriptEntry::Byte(0x05),
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
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_panics_hashing_with_blake3_160_keyed_with_invalid_utf8_key() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar), // Key
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0x9d),
                ScriptEntry::Byte(0xa4),
                ScriptEntry::Byte(0xef),
                ScriptEntry::Byte(0xb8),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Value
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_160Keyed),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];

        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_hashes_with_blake3_160internal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_160Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_160Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_160_internal(&term, key);
            assert_eq!(hashed_term.size(), 20);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_256internal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_256Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_256Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_256_internal(&term, key);
            assert_eq!(hashed_term.size(), 32);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_512_internal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_512Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_512Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_512_internal(&term, key);
            assert_eq!(hashed_term.size(), 64);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake3_256_160_internal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake3_256_160Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake3_256_160Internal),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake3_256_160_internal(&term, key);
            assert_eq!(hashed_term.size(), 20);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_hashes_with_blake2s_256() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Blake2s256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Blake2s256),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let test_terms = vec![VmTerm::Unsigned8(0x01), VmTerm::Signed8(-1)];

        let mut script_output: Vec<VmTerm> = vec![];
        for term in test_terms {
            let hashed_term = bifs::blake2s_256(&term);
            assert_eq!(hashed_term.size(), 32);
            script_output.push(hashed_term);
        }

        let base: TestBaseArgs = get_test_base_args(&mut ss, 30, script_output, 0, key);
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
    fn it_adds_two_numbers() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Add),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFE),
                ScriptEntry::Opcode(OP::Add),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Add),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x03),
            VmTerm::Signed8(-3),
            VmTerm::Signed8(0),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_panics_if_add_not_same_type() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Add),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x03),
            VmTerm::Signed8(-3),
            VmTerm::Signed8(0),
        ];
        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_adds_to_array() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Add),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned8Array(vec![0x01, 0x02, 0x03, 0x04])];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_subs_two_numbers() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Sub),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFE),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Sub),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Sub),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01),
            VmTerm::Signed8(1),
            VmTerm::Signed8(-2),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_subs_from_array() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Sub),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![0x01, 0x02])];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_subs_array_from_array() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x0A),
                ScriptEntry::Byte(0x14),
                ScriptEntry::Opcode(OP::Sub),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![0x08, 0x11])];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_subs_array_from_array_overflow() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x0A),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Sub),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![0x08, 0x11])];
        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_multiples_array_with_number() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![0x04, 0x6])];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_multiples_array_with_array() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![0x04, 0x09])];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_multiplies_array_with_array_overflow() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![])];
        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_cannot_multiply_two_arrays_with_different_length() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_multiplies_two_numbers() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFE),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Mult),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x06),
            VmTerm::Signed8(2),
            VmTerm::Signed8(-1),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_divides_two_numbers() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFE),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFC),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xFF),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x02),
            VmTerm::Signed8(0x02),
            VmTerm::Signed8(-1),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_divides_array_with_number() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![VmTerm::Unsigned8Array(vec![0x02, 0x4])];
        assert_script_ok(ss, script_output, key);

        let ss_2 = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Signed8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xFE),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output_2: Vec<VmTerm> = vec![VmTerm::Signed8Array(vec![0x00, -1])];
        assert_script_ok(ss_2, script_output_2, key);
    }

    #[test]
    fn it_divides_array_with_another_array() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8ArrayVar),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xFE),
                ScriptEntry::Opcode(OP::Signed8ArrayVar),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xFC),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![1, 1]),
            VmTerm::Signed8Array(vec![2]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_divides_array_with_another_array_overflow() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Byte(0x08),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Div),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_returns_min() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::Min),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Min),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xaa),
                ScriptEntry::Byte(0xaa),
                ScriptEntry::Opcode(OP::Min),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Opcode(OP::Min),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x05),
            VmTerm::Unsigned8(0x03),
            VmTerm::Unsigned16(0xaaaa),
            VmTerm::Unsigned16(0xeeee),
            VmTerm::Unsigned8(0x02),
            VmTerm::Unsigned8(0x02),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_returns_max() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x06),
                ScriptEntry::Opcode(OP::Max),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x09),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Max),
                ScriptEntry::Opcode(OP::Nop),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Byte(0xff),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xaa),
                ScriptEntry::Byte(0xaa),
                ScriptEntry::Opcode(OP::Max),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Byte(0xee),
                ScriptEntry::Opcode(OP::Max),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x06),
            VmTerm::Unsigned8(0x09),
            VmTerm::Unsigned16(0xffff),
            VmTerm::Unsigned16(0xeeee),
            VmTerm::Unsigned8(0x02),
            VmTerm::Unsigned8(0x02),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_checks_within() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var), // Case 1: 2 <= 3 < 4 => true
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Within),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Case 2: 2 <= 2 < 4 => true
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Within),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Case 3: 2 <= 1 < 4 => false
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Within),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Case 4: 2 <= 4 < 4 => false
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Within),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned8Var), // Case 5: 2 <= 5 < 4 => false
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x05),
                ScriptEntry::Opcode(OP::Within),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x01), // true
            VmTerm::Unsigned8(0x01), // true
            VmTerm::Unsigned8(0x00), // false
            VmTerm::Unsigned8(0x00), // false
            VmTerm::Unsigned8(0x00), // false
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_fails_within_check() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Within),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::InvalidArgs);
    }

    #[test]
    fn it_inverts_bits_primitives() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned64Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned128Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed16Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed32Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed64Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed128Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8(0x1d),
            VmTerm::Unsigned16(0x3c1d),
            VmTerm::Unsigned32(0x3c1d_3c1d),
            VmTerm::Unsigned64(0x3c1d_3c1d_3c1d_3c1d),
            VmTerm::Unsigned128(0x3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d),
            VmTerm::Signed8(0x1d),
            VmTerm::Signed16(0x3c1d),
            VmTerm::Signed32(0x3c1d_3c1d),
            VmTerm::Signed64(0x3c1d_3c1d_3c1d_3c1d),
            VmTerm::Signed128(0x3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_inverts_bits_arrays() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned32ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned64ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned128ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed32ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed64ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Signed128ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::BitInvert),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x1d, 0x1d]),
            VmTerm::Unsigned16Array(vec![0x3c1d, 0x3c1d]),
            VmTerm::Unsigned32Array(vec![0x3c1d_3c1d, 0x3c1d_3c1d]),
            VmTerm::Unsigned64Array(vec![0x3c1d_3c1d_3c1d_3c1d, 0x3c1d_3c1d_3c1d_3c1d]),
            VmTerm::Unsigned128Array(vec![
                0x3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d,
                0x3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d,
            ]),
            VmTerm::Signed8Array(vec![0x1d, 0x1d]),
            VmTerm::Signed16Array(vec![0x3c1d, 0x3c1d]),
            VmTerm::Signed32Array(vec![0x3c1d_3c1d, 0x3c1d_3c1d]),
            VmTerm::Signed64Array(vec![0x3c1d_3c1d_3c1d_3c1d, 0x3c1d_3c1d_3c1d_3c1d]),
            VmTerm::Signed128Array(vec![
                0x3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d,
                0x3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d_3c1d,
            ]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_ors_primitives() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Opcode(OP::BitOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned8(0xf3), VmTerm::Unsigned16(0xebf3)];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_ors_arrays() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Opcode(OP::BitOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0xf3, 0xf3]),
            VmTerm::Unsigned16Array(vec![0xebf3, 0xebf3]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_xors_primitives() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Opcode(OP::BitXOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitXOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned8(0x11), VmTerm::Unsigned16(0x6811)];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_xors_arrays() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Opcode(OP::BitXOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Byte(0xe2),
                ScriptEntry::Byte(0xc3),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitXOR),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x11, 0x11]),
            VmTerm::Unsigned16Array(vec![0x6811, 0x6811]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_shifts_left_primitives() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x6e),
                ScriptEntry::Opcode(OP::BitSHLeft),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitSHLeft),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned8(0xb8), VmTerm::Unsigned16(0x5f98)];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_shifts_left_arrays() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Opcode(OP::BitSHLeft),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitSHLeft),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0xcc, 0x98]),
            VmTerm::Unsigned16Array(vec![0x57e6, 0xafcc]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_shifts_right_primitives() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x6e),
                ScriptEntry::Opcode(OP::BitSHRight),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitSHRight),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> =
            vec![VmTerm::Unsigned8(0x1b), VmTerm::Unsigned16(0x157e)];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_shifts_right_arrays() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x03),
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Opcode(OP::BitSHRight),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::Unsigned16ArrayVar),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Byte(0xf3),
                ScriptEntry::Byte(0xab),
                ScriptEntry::Opcode(OP::BitSHRight),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };

        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x3c, 0x1e]),
            VmTerm::Unsigned16Array(vec![0x55f9, 0x2afc]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Trap),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_traps_if_value_equals_to_one() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIf),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_value_doenst_equal_one() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIf),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_values_equal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfEq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_values_are_not_equal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfEq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_values_are_not_equal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfNeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_values_are_equal() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfNeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_top_item_is_less_or_equal_to_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfLeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_traps_if_top_item_is_less_or_equal_to_second_2() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfLeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_is_not_less_or_equal_to_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfLeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_top_item_is_greater_or_equal_to_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfGeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_traps_if_top_item_is_greater_or_equal_to_second_2() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfGeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_is_not_greater_or_equal_to_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfGeq),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_top_item_is_less_than_the_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfLt),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_is_not_less_than_the_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfLt),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_is_not_less_than_the_second_2() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfLt),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_top_item_is_greater_than_the_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::TrapIfGt),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_is_not_greater_than_the_second() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfGt),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_is_not_greater_than_the_second_2() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Opcode(OP::Unsigned8Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfGt),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_traps_if_top_item_type_is_not_same_as_given() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfNeqType),
                ScriptEntry::Byte(0xaa),
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(0x0404_0404),
            VmTerm::Unsigned32(0x0101_0101),
        ];
        assert_script_fail(ss, script_output, key, ExecutionResult::Panic);
    }

    #[test]
    fn it_doesnt_trap_if_top_item_type_is_same_as_given() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::Unsigned16Var),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Byte(0x01),
                ScriptEntry::Opcode(OP::TrapIfNeqType),
                ScriptEntry::Byte(0x04), // Type for Unsigned16Var
                ScriptEntry::Opcode(OP::Unsigned32Var),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned32(0x0404_0404),
            VmTerm::Unsigned32(0x0101_0101),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_substr() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Substr),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Substr),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Substr),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x75, 0xaf, 0xf6, 0xa5]), // Substr 0 -> 1st 0 elems, 2nd 4 elems (inverted logic)
            VmTerm::Unsigned8Array(vec![]),
            VmTerm::Unsigned8Array(vec![0xf6, 0xa5]), // Substr 2 -> 1st = 2 elems, 2nd = 2 elems (inverted logic)
            VmTerm::Unsigned8Array(vec![0x75, 0xaf]),
            VmTerm::Unsigned8Array(vec![]), // Substr 4 -> 1st 4 elems, 2nd 0 elems (inverted logic)
            VmTerm::Unsigned8Array(vec![0x75, 0xaf, 0xf6, 0xa5]),
        ];
        assert_script_ok(ss, script_output, key);
    }

    #[test]
    fn it_panics_substr_if_mid_greater_than_len() {
        let key = "test_key";
        let mut ss = Script {
            script: vec![
                ScriptEntry::Byte(0x03), // 3 arguments are pushed onto the stack: out_amount, out_address, out_script_hash
                ScriptEntry::Opcode(OP::Unsigned8ArrayVar),
                ScriptEntry::Byte(0x04),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x75),
                ScriptEntry::Byte(0xaf),
                ScriptEntry::Byte(0xf6),
                ScriptEntry::Byte(0xa5),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Dup),
                ScriptEntry::Opcode(OP::Substr),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Substr),
                ScriptEntry::Byte(0x02),
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::Substr),
                ScriptEntry::Byte(0x05), // Bound overflow
                ScriptEntry::Byte(0x00),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PopToScriptOuts),
                ScriptEntry::Opcode(OP::PushOut),
                ScriptEntry::Opcode(OP::Verify),
            ],
            ..Script::default()
        };
        let mut script_output: Vec<VmTerm> = vec![
            VmTerm::Unsigned8Array(vec![0x75, 0xaf, 0xf6, 0xa5]),
            VmTerm::Unsigned8Array(vec![]),
            VmTerm::Unsigned8Array(vec![0xf6, 0xa5]),
            VmTerm::Unsigned8Array(vec![0x75, 0xaf]),
        ];
        assert_script_fail(ss, script_output, key, ExecutionResult::IndexOutOfBounds);
    }
}
