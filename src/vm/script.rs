// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::SCRIPT_LIMIT_OPCODES;
use crate::primitives::{Address, Hash160, Input, Output};
use crate::vm::internal::VmTerm;
use crate::vm::opcodes::OP;
use bincode::{Decode, Encode};
use ibig::ibig;
use num_traits::{FromPrimitive, ToPrimitive};
use rand::prelude::*;
use rand_pcg::Pcg64;
use rand_seeder::Seeder;
use std::collections::HashMap;

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
    ($exp:expr, $frame:expr, $frame_stack:expr, $structt:expr) => {
        if $exp == &1 {
            return Ok(ExecutionResult::Ok).into();
        } else {
            let mut stack_trace = StackTrace::default();
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
            return Err((ExecutionResult::Invalid, stack_trace)).into();
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

                        ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8Var) => {
                            frame.i_ptr += 1;
                            let i = &f.script[frame.i_ptr];

                            match i {
                                ScriptEntry::Byte(byte) => {
                                    frame.stack.push(VmTerm::Unsigned8(*byte));
                                    frame.executor.state = ScriptExecutorState::ExpectingInitialOP;
                                    frame.i_ptr += 1;
                                }

                                ScriptEntry::Opcode(op) => {
                                    frame.executor.state = ScriptExecutorState::Error(
                                        ExecutionResult::BadFormat,
                                        (frame.i_ptr, frame.func_idx, *op, frame.stack.as_slice())
                                            .into(),
                                    );
                                }
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
                        stack_trace.extend_from_frame_stack(&frame_stack[..fs_len - 1], self);
                        return Err((result, stack_trace)).into();
                    }
                },
            }

            if exec_count > SCRIPT_LIMIT_OPCODES {
                let mut stack_trace = StackTrace::default();
                let i_ptr = frame_stack.last().unwrap().i_ptr;
                let fs_len = frame_stack.len();
                stack_trace.trace.push(
                    (
                        i_ptr,
                        frame_stack.last().unwrap().func_idx,
                        self.script[i_ptr].clone(),
                    )
                        .into(),
                );
                stack_trace.extend_from_frame_stack(&frame_stack[..fs_len - 1], self);
                return Err((ExecutionResult::OutOfGas, stack_trace)).into();
            }

            if memory_size > MEMORY_SIZE {
                let mut stack_trace = StackTrace::default();
                let i_ptr = frame_stack.last().unwrap().i_ptr;
                let fs_len = frame_stack.len();
                stack_trace.trace.push(
                    (
                        i_ptr,
                        frame_stack.last().unwrap().func_idx,
                        self.script[i_ptr].clone(),
                    )
                        .into(),
                );
                stack_trace.extend_from_frame_stack(&frame_stack[..fs_len - 1], self);
                return Err((ExecutionResult::OutOfMemory, stack_trace)).into();
            }

            if pop_frame {
                let frame = frame_stack.pop().unwrap();
                let fs_len = frame_stack.len();

                // Check the top of the stack for the execution result
                if fs_len == 0 {
                    if frame.stack.is_empty() {
                        let mut stack_trace = StackTrace::default();
                        stack_trace.trace.push(
                            (
                                frame.i_ptr - 1,
                                frame.func_idx,
                                self.script[frame.i_ptr - 1].clone(),
                            )
                                .into(),
                        );
                        return Err((ExecutionResult::Invalid, stack_trace)).into();
                    }

                    let top = &frame.stack[0];

                    match top {
                        VmTerm::Signed8(v) => check_top_stack_val!(v, frame, frame_stack, self),
                        VmTerm::Signed16(v) => check_top_stack_val!(v, frame, frame_stack, self),
                        VmTerm::Signed32(v) => check_top_stack_val!(v, frame, frame_stack, self),
                        VmTerm::Signed64(v) => check_top_stack_val!(v, frame, frame_stack, self),
                        VmTerm::Signed128(v) => check_top_stack_val!(v, frame, frame_stack, self),
                        VmTerm::SignedBig(v) => {
                            if v == &ibig!(1) {
                                return Ok(ExecutionResult::Ok).into();
                            } else {
                                let mut stack_trace = StackTrace::default();
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
                                return Err((ExecutionResult::Invalid, stack_trace)).into();
                            }
                        }
                        _ => {
                            let mut stack_trace = StackTrace::default();
                            stack_trace.trace.push(
                                (
                                    frame.i_ptr - 1,
                                    frame.func_idx,
                                    self.script[frame.i_ptr - 1].clone(),
                                )
                                    .into(),
                            );
                            stack_trace.extend_from_frame_stack(&frame_stack, self);
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
                            stack_trace.trace.push(
                                (
                                    frame.i_ptr - 1,
                                    frame.func_idx,
                                    self.script[frame.i_ptr - 1].clone(),
                                )
                                    .into(),
                            );
                            stack_trace.extend_from_frame_stack(&frame_stack, self);
                            return Err((ExecutionResult::StackOverflow, stack_trace)).into();
                        }
                    }
                }
            }

            if let Some(new_frame) = new_frame {
                if frame_stack.len() > MAX_FRAMES {
                    let frame = frame_stack.last().unwrap();
                    let mut stack_trace = StackTrace::default();
                    stack_trace.trace.push(
                        (
                            frame.i_ptr,
                            frame.func_idx,
                            self.script[new_frame.i_ptr].clone(),
                        )
                            .into(),
                    );
                    stack_trace.extend_from_frame_stack(&frame_stack, self);
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
                            } else {
                                let mut output = Output {
                                    amount,
                                    address: Some(address.clone()),
                                    script_hash: script_hash.clone(),
                                    coinbase_height: None,
                                    coloured_address: None,
                                    inputs_hash: inputs_hash.clone(),
                                    idx: output_stack.len() as u16,
                                    script_outs: vec![],
                                    hash: None,
                                };

                                output.compute_hash(key);
                                output_stack_idx_map
                                    .insert((address, script_hash), output_stack.len() as u16);
                                output_stack.push(output);
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
                            } else {
                                let mut output = Output {
                                    amount,
                                    address: Some(address.clone()),
                                    script_hash: script_hash.clone(),
                                    coinbase_height: None,
                                    coloured_address: None,
                                    inputs_hash: inputs_hash.clone(),
                                    idx: output_stack.len() as u16,
                                    script_outs: vec![],
                                    hash: None,
                                };

                                output.compute_hash(key);
                                output_stack_idx_map
                                    .insert((address, script_hash), output_stack.len() as u16);
                                output_stack.push(output);

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
                    let address = exec_stack.pop().unwrap();
                    let script_hash = exec_stack.pop().unwrap();
                    let coinbase_height = exec_stack.pop().unwrap();

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
                                script_outs: vec![],
                                hash: None,
                            };

                            output.compute_hash(key);
                            output_stack.push(output);

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

                ScriptEntry::Opcode(OP::BreakIfEq) => {
                    if exec_stack.len() < 2 {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let e_stack_len = exec_stack.len();
                    let e1 = exec_stack.pop().unwrap();
                    let e2 = exec_stack.pop().unwrap();

                    if e1 == e2 {
                        self.state = ScriptExecutorState::BreakLoop;
                    }
                }

                ScriptEntry::Opcode(OP::Continue) => {
                    self.state = ScriptExecutorState::ContinueLoop;
                }

                ScriptEntry::Opcode(OP::End) => {
                    self.state = ScriptExecutorState::EndBlock;
                }

                ScriptEntry::Opcode(OP::Pick) => {
                    self.state = ScriptExecutorState::ExpectingIndexU8(OP::Pick);
                }

                ScriptEntry::Opcode(OP::Unsigned8Var) => {
                    self.state = ScriptExecutorState::ExpectingBytesOrCachedTerm(OP::Unsigned8Var);
                }

                ScriptEntry::Opcode(OP::Add1) => {
                    if exec_stack.is_empty() {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }

                    let mut last = exec_stack.last_mut().unwrap();
                    if last.add_one().is_some() {
                        self.state = ScriptExecutorState::ExpectingInitialOP;
                    } else {
                        self.state = ScriptExecutorState::Error(
                            ExecutionResult::InvalidArgs,
                            (i_ptr, func_idx, op.clone(), exec_stack.as_slice()).into(),
                        );
                    }
                }

                ScriptEntry::Opcode(OP::ClearStack) => {
                    exec_stack.clear();
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
    pub fn extend_from_frame_stack<'a>(&mut self, stack: &[Frame<'a>], script: &Script) {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use rayon::prelude::*;

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
            ss.execute(&args, &ins, &mut outs, &mut idx_map, [0; 32], key),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, vec![oracle_out]);
    }

    #[test]
    fn it_breaks_loop() {
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
        }]
        .iter()
        .cloned()
        .map(|mut i| {
            i.compute_hash(key);
            i
        })
        .collect::<Vec<_>>();
        let mut outs = vec![];

        let ins_hashes: Vec<u8> = ins.iter_mut().fold(vec![], |mut acc, v: &mut Input| {
            v.compute_hash(key);
            acc.extend(v.hash().unwrap().0);
            acc
        });

        let inputs_hash = Hash160::hash_from_slice(ins_hashes.as_slice(), key);

        let inputs_hash: Hash160 = ins.iter().cloned().cycle().take(2).fold(
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
            amount: 90,
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
            ss.execute(&args, &ins, &mut outs, &mut idx_map, [0; 32], key),
            Ok(ExecutionResult::OkVerify).into()
        );
        assert_eq!(outs, vec![oracle_out]);
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
            ss.execute(&args, ins.as_slice(), &mut outs, &mut idx_map, [0; 32], key),
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
            ss.execute(&args, &ins, &mut outs, &mut idx_map, [0; 32], key),
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
            ss.execute(&args, &ins, &mut outs, &mut idx_map, [0; 32], key),
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
}
