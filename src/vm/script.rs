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
use std::collections::HashMap;

/// Max frame stack size
pub const MAX_FRAMES: usize = 128;

/// Max stack size
pub const STACK_SIZE: usize = 256;

/// VM max memory size in bytes
pub const MEMORY_SIZE: usize = 512_000;

/// Max output stack size
pub const MAX_OUT_STACK: usize = 1_000;

macro_rules! check_top_stack_val {
    ($exp:expr) => {
        if $exp == &1 {
            return ExecutionResult::Ok;
        } else {
            return ExecutionResult::Invalid;
        }
    };
}

#[derive(PartialEq, Debug, Clone)]
enum ScriptEntry {
    Opcode(OP),
    Byte(u8),
}

#[derive(Debug, Clone)]
struct Frame<'a> {
    pub stack: Vec<VmTerm>,
    pub i_ptr: usize,
    pub func_idx: usize,
    pub s_executor: ScriptExecutor<'a>,
}

impl<'a> Frame<'a> {
    pub fn new(func_idx: usize) -> Self {
        Self {
            stack: Vec::with_capacity(STACK_SIZE),
            i_ptr: 0,
            func_idx,
            s_executor: ScriptExecutor::new(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Script {
    version: u8,
    script: Vec<ScriptEntry>,
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
                ScriptEntry::Opcode(OP::PushCoinbaseOut),
            ],
        }
    }

    pub fn new_coinbase_with_extra_data() -> Script {
        Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x06), // 6 arguments are pushed onto the stack: out_amount, out_address, out_script_hash, coinbase_height, extra_nonce, extra_data
                ScriptEntry::Opcode(OP::PushCoinbaseOut),
            ],
        }
    }

    pub fn new_coinbase_without_spending_address_with_extra_data() -> Script {
        Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x05), // 5 arguments are pushed onto the stack: out_amount, out_script_hash, coinbase_height, extra_nonce, extra_data
                ScriptEntry::Opcode(OP::PushCoinbaseOut),
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

    pub fn new_simple_coloured_spend() -> Script {
        Script {
            version: 1,
            script: vec![
                ScriptEntry::Byte(0x04), // 4 arguments are pushed onto the stack: out_amount, out_address, out_colour_hash, out_script_hash
                ScriptEntry::Opcode(OP::PushOutVerify),
            ],
        }
    }

    pub fn execute(
        &self,
        args: &[VmTerm],
        input_stack: &[Input],
        output_stack: &mut Vec<Output>,
        key: &str,
    ) -> ExecutionResult {
        if self.version > 1 {
            return ExecutionResult::Ok;
        }

        if args.len() > 256 {
            return ExecutionResult::TooManyArgs;
        }

        if self.version == 0 {
            return ExecutionResult::BadVersion;
        }

        let funcs = match self.parse_funcs() {
            Ok(funcs) => funcs,
            Err(r) => return r,
        };
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

            if let Some(frame) = frame_stack.last_mut() {
                let f = &funcs[frame.func_idx];

                if frame.i_ptr >= f.script.len() {
                    pop_frame = true
                } else {
                    let i = &f.script[frame.i_ptr];

                    frame.s_executor.push_op(
                        i,
                        &inputs_hash,
                        &mut memory_size,
                        &mut frame.stack,
                        input_stack,
                        output_stack,
                        key,
                    );

                    match frame.s_executor.done() {
                        None => {}
                        Some(result) => return result,
                    }

                    frame.i_ptr += 1;
                    exec_count += 1;
                }
            } else {
                unreachable!();
            }

            if exec_count > SCRIPT_LIMIT_OPCODES {
                return ExecutionResult::OutOfGas;
            }

            if memory_size > MEMORY_SIZE {
                return ExecutionResult::OutOfMemory;
            }

            if pop_frame {
                let frame = frame_stack.pop().unwrap();
                let fs_len = frame_stack.len();

                // Check the top of the stack for the execution result
                if fs_len == 0 {
                    if frame.stack.is_empty() {
                        return ExecutionResult::Invalid;
                    }

                    let top = &frame.stack[0];

                    match top {
                        VmTerm::Signed8(v) => check_top_stack_val!(v),
                        VmTerm::Signed16(v) => check_top_stack_val!(v),
                        VmTerm::Signed32(v) => check_top_stack_val!(v),
                        VmTerm::Signed64(v) => check_top_stack_val!(v),
                        VmTerm::Signed128(v) => check_top_stack_val!(v),
                        VmTerm::SignedBig(v) => {
                            if v == &ibig!(1) {
                                return ExecutionResult::Ok;
                            } else {
                                return ExecutionResult::Invalid;
                            }
                        }
                        _ => return ExecutionResult::Ok,
                    }
                } else {
                    let top = &mut frame_stack[fs_len - 1].stack;

                    if top.len() + frame.stack.len() > STACK_SIZE {
                        return ExecutionResult::StackOverflow;
                    }

                    // Push terms on top frame
                    for t in frame.stack.iter().rev().cloned() {
                        top.push(t);
                    }
                }
            }

            if let Some(new_frame) = new_frame {
                if frame_stack.len() > MAX_FRAMES {
                    return ExecutionResult::StackOverflow;
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
                    match op {
                        ScriptEntry::Opcode(OP::End) => return Err(ExecutionResult::BadFormat),
                        ScriptEntry::Opcode(OP::Func) => return Err(ExecutionResult::BadFormat),
                        op_or_byte => out_script.script.push(op_or_byte.clone()),
                    }
                }

                out.push(out_script);
            }

            _ => return Err(ExecutionResult::BadFormat),
        }

        Ok(out)
    }
}

#[derive(Debug, Clone)]
struct ScriptExecutor<'a> {
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
        inputs_hash: &Hash160,
        memory_size: &mut usize,
        exec_stack: &mut Vec<VmTerm>,
        input_stack: &[Input],
        output_stack: &mut Vec<Output>,
        //output_stack_idx: &mut HashMap<(Address, Hash160), u16>,
        key: &str,
    ) {
        match self.state {
            ScriptExecutorState::ExpectingArgsLen => match op {
                ScriptEntry::Byte(args_len) => {
                    let args_len = *args_len as usize;
                    if exec_stack.len() != args_len {
                        self.state = ScriptExecutorState::Error(ExecutionResult::BadFormat);
                        return;
                    }

                    self.state = ScriptExecutorState::ExpectingInitialOP;
                }

                _ => {
                    self.state = ScriptExecutorState::Error(ExecutionResult::BadFormat);
                }
            },

            ScriptExecutorState::ExpectingInitialOP => match op {
                ScriptEntry::Byte(_) => {
                    self.state = ScriptExecutorState::Error(ExecutionResult::BadFormat);
                }

                ScriptEntry::Opcode(OP::PushOut) => {
                    if exec_stack.len() < 3 {
                        self.state = ScriptExecutorState::Error(ExecutionResult::InvalidArgs);
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
                            let mut output = Output {
                                amount,
                                address: Some(Address(addr)),
                                script_hash: Hash160(script_hash),
                                coinbase_height: None,
                                coloured_address: None,
                                inputs_hash: inputs_hash.clone(),
                                idx: output_stack.len() as u16,
                                script_outs: exec_stack.clone(),
                                hash: None,
                            };

                            output.compute_hash(key);
                            output_stack.push(output);

                            if output_stack.len() > MAX_OUT_STACK {
                                self.state =
                                    ScriptExecutorState::Error(ExecutionResult::OutStackOverflow);
                                return;
                            }

                            self.state = ScriptExecutorState::ExpectingInitialOP;
                        }

                        _ => {
                            self.state = ScriptExecutorState::Error(ExecutionResult::InvalidArgs);
                        }
                    }
                }

                ScriptEntry::Opcode(OP::PushOutVerify) => {
                    if exec_stack.len() < 3 {
                        self.state = ScriptExecutorState::Error(ExecutionResult::InvalidArgs);
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
                            let mut output = Output {
                                amount,
                                address: Some(Address(addr)),
                                script_hash: Hash160(script_hash),
                                coinbase_height: None,
                                coloured_address: None,
                                inputs_hash: inputs_hash.clone(),
                                idx: output_stack.len() as u16,
                                script_outs: exec_stack.clone(),
                                hash: None,
                            };

                            output.compute_hash(key);
                            output_stack.push(output);

                            if output_stack.len() > MAX_OUT_STACK {
                                self.state =
                                    ScriptExecutorState::Error(ExecutionResult::OutStackOverflow);
                                return;
                            }

                            self.state = ScriptExecutorState::OkVerify;
                        }

                        _ => {
                            self.state = ScriptExecutorState::Error(ExecutionResult::InvalidArgs);
                        }
                    }
                }

                ScriptEntry::Opcode(OP::PushCoinbaseOut) => {
                    if exec_stack.len() < 4 {
                        self.state = ScriptExecutorState::Error(ExecutionResult::InvalidArgs);
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
                                script_outs: exec_stack.clone(),
                                hash: None,
                            };

                            output.compute_hash(key);
                            output_stack.push(output);

                            if output_stack.len() > MAX_OUT_STACK {
                                self.state =
                                    ScriptExecutorState::Error(ExecutionResult::OutStackOverflow);
                                return;
                            }

                            self.state = ScriptExecutorState::ExpectingInitialOP;
                        }

                        _ => {
                            self.state = ScriptExecutorState::Error(ExecutionResult::InvalidArgs);
                        }
                    }
                }

                ScriptEntry::Opcode(OP::Verify) => {
                    self.state = ScriptExecutorState::OkVerify;
                }

                ScriptEntry::Opcode(_) => {
                    self.state = ScriptExecutorState::Error(ExecutionResult::BadFormat);
                }
            },

            _ => unimplemented!(),
        }
    }

    #[inline]
    pub fn done(&self) -> Option<ExecutionResult> {
        match self.state {
            ScriptExecutorState::OkVerify => Some(ExecutionResult::OkVerify),
            ScriptExecutorState::Error(res) => Some(res),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
enum ScriptExecutorState<'a> {
    ExpectingArgsLen,
    ExpectingInitialOP,
    ExpectingBytesOrCachedTerm,
    ExpectingInitialOPorOPs(&'a [OP]),
    OkVerify,
    Error(ExecutionResult),
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
                Some(OP::Float32Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Float32Var));
                    self.state = ScriptParserState::ExpectingBytes(4);
                    Ok(())
                }
                Some(OP::Float64Var) => {
                    self.out.push(ScriptEntry::Opcode(OP::Float64Var));
                    self.state = ScriptParserState::ExpectingBytes(8);
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
                        OP::Unsigned32ArrayVar | OP::Signed32ArrayVar | OP::Float32ArrayVar => {
                            self.state = ScriptParserState::ExpectingBytes((*sum * 4) as usize);
                            Ok(())
                        }
                        OP::Unsigned64ArrayVar | OP::Signed64ArrayVar | OP::Float64ArrayVar => {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_simple_spends() {
        let key = "test_key";
        let ss = Script::new_simple_spend();
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
            ss.execute(&args, &ins, &mut outs, key),
            ExecutionResult::OkVerify
        );
        assert_eq!(outs, vec![oracle_out]);
    }

    #[test]
    fn pushout_zero_amount() {
        let key = "test_key";
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
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
            ss.execute(&args, &ins, &mut outs, key),
            ExecutionResult::InvalidArgs
        );
    }

    #[test]
    fn pushout_neg_amount() {
        let key = "test_key";
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
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
            ss.execute(&args, &ins, &mut outs, key),
            ExecutionResult::InvalidArgs
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
