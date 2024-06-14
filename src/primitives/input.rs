// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{Shard, ShardBackend};
use crate::consensus::{Money, BLOCK_HORIZON};
use crate::primitives::{
    Address, AddressAndHash160, Hash160, Hash160Algo, Hash256, OutWitnessVec, Output, PublicKey,
    TxVerifyErr,
};
use crate::settings::SETTINGS;
use crate::vm::internal::VmTerm;
use crate::vm::{
    ExecutionResult, Script, SigVerificationErr, VerificationStack, VmFlags, VmResult,
};
use accumulator::group::{Codec, Rsa2048};
use accumulator::Witness;
use bincode::{Decode, Encode};
use merkletree::proof::Proof;
use schnorrkel::{PublicKey as SchnorPK, Signature as SchnorSig};
use std::collections::HashMap;
use typenum::U2;

const COLOUR_HASH_KEY: &str = "colour";

#[derive(PartialEq, Debug, Clone)]
pub struct Input {
    /// Output. Is null if this is a coinbase input
    pub out: Option<Output>,

    /// Spending public key. Is null if no spending public key is required or if this is a coinbase input.
    /// Present in a coloured coinbase input.
    pub spending_pkey: Option<PublicKey>,

    /// Output witness. Is null if this is a coinbase input
    pub witness: Option<Witness<Rsa2048, Output>>,

    /// Spending script
    pub script: Script,

    /// Additional spend script for coloured outputs. Can be used to limit the ability to spend a particular token
    pub colour_script: Option<Script>,

    /// Spend script arguments
    pub script_args: Vec<VmTerm>,

    /// Colour spend script arguments
    pub colour_script_args: Option<Vec<VmTerm>>,

    /// Merkle spend proof of address + script hash if spend key is present
    ///
    /// Otherwise this is the merkle proof of a script hash
    pub spend_proof: Option<(Vec<Hash160>, Vec<u64>)>,

    /// Merkle colour spend proof of colour script hash
    pub colour_proof: Option<(Vec<Hash160>, Vec<u64>)>,

    /// Block height chosen by the coinbase emitter for coinbase idempotency. Without it,
    /// an attacker can replay the transaction and emit more coins than intended.
    ///
    /// The coinbase transaction is only valid while this value is greater than the `BLOCK_HORIZON`
    ///
    /// Must be greater or equal to `current_height - BLOCK_HORIZON`.
    pub coloured_coinbase_block_height: Option<u64>,

    /// Additional nonce for coloured coinbases, in order to be able to create as many coloured coinbases
    /// as necessary. Must be unique per `coloured_coinbase_block_height`.
    pub coloured_coinbase_nonce: Option<u32>,

    /// Input hash. Not serialised
    pub hash: Option<Hash256>,

    /// Input flags. Not serialised
    pub input_flags: InputFlags,
}

impl Default for Input {
    fn default() -> Self {
        Self {
            out: None,
            spending_pkey: None,
            witness: None,
            script: Script::default(),
            colour_script: None,
            script_args: vec![],
            colour_script_args: None,
            spend_proof: None,
            colour_proof: None,
            coloured_coinbase_block_height: None,
            coloured_coinbase_nonce: None,
            hash: None,
            input_flags: InputFlags::IsCoinbase,
        }
    }
}

impl Input {
    /// Serialize to bytes
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    /// Serializes to bytes for signing. Will not encode any script args or the out witness
    #[must_use]
    pub fn to_bytes_for_signing(&self) -> Vec<u8> {
        let mut copied = self.clone();

        // We don't sign the witness as it can be recomputed by miners
        copied.witness = None;

        // We also don't sign the script arguments marked as malleable
        let mut i = 0;
        let mut r = 0;
        while i + r < copied.script.malleable_args.len() {
            if copied.script.malleable_args[i + r] {
                copied.script_args.remove(i);
                r += 1;
            } else {
                i += 1;
            }
        }
        if let Some(script) = &self.colour_script {
            i = 0;
            r = 0;
            let args = copied.colour_script_args.as_mut().unwrap();
            while i + r < script.malleable_args.len() {
                if script.malleable_args[i + r] {
                    args.remove(i);
                    r += 1;
                } else {
                    i += 1;
                }
            }
        }

        crate::codec::encode_to_vec(&copied).unwrap()
    }

    pub fn compute_hash(&mut self, key: &str) {
        if self.hash.is_some() {
            return;
        }

        let bytes = self.to_bytes();
        self.hash = Some(Hash256::hash_from_slice(bytes, key));
    }

    #[must_use]
    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    #[must_use]
    pub fn out(&self) -> Option<&Output> {
        self.out.as_ref()
    }

    #[must_use]
    pub fn is_coinbase(&self) -> bool {
        self.input_flags == InputFlags::IsCoinbase
    }

    #[must_use]
    pub fn is_coloured(&self) -> bool {
        self.colour_script.is_some()
    }

    #[must_use]
    pub fn is_failable(&self) -> bool {
        match self.input_flags {
            InputFlags::FailablePlain
            | InputFlags::FailablePlainWithoutSpendKey
            | InputFlags::FailableHasSpendProof
            | InputFlags::FailableIsColoured
            | InputFlags::FailableIsColouredHasColourProof
            | InputFlags::FailableIsColouredHasSpendProof
            | InputFlags::FailableIsColouredHasSpendProofAndColourProof
            | InputFlags::FailableHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredWithoutSpendKey
            | InputFlags::FailableIsColouredHasColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofAndColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbase
            | InputFlags::FailableIsColouredCoinbaseHasColourProof
            | InputFlags::FailableIsColouredCoinbaseHasSpendProof
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProof
            | InputFlags::FailableIsColouredCoinbaseWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey => {
                true
            }
            _ => false,
        }
    }

    pub fn verify(
        &self,
        key: &str,
        height: u64,
        chain_id: u8,
        ins_sum: &mut Money,
        outs_sum: &mut Money,
        coloured_ins_sums: &mut HashMap<Hash160, Money>,
        coloured_outs_sums: &mut HashMap<Hash160, Money>,
        timestamp: i64,
        block_reward: &Money,
        prev_block_hash: Hash256,
        coinbase_allowed: bool,
        to_add: &mut Vec<Output>,
        to_delete: &mut OutWitnessVec,
        ver_stack: &mut VerificationStack,
        idx_map: &mut HashMap<Hash160, u16>,
        seed_bytes: &[u8],
        input_stack: &[Self],
        validate_coloured_coinbase_idempotency: fn(&Self) -> Result<(), TxVerifyErr>,
    ) -> Result<(), TxVerifyErr> {
        match self.input_flags {
            InputFlags::IsCoinbase => {
                if !coinbase_allowed {
                    return Err(TxVerifyErr::CoinbaseNotAllowed);
                }

                let script = Script::new_coinbase();

                let a1 = &self.script_args[0];
                let a4 = &self.script_args[3];

                // Validate terms
                match (a1, a4) {
                    (VmTerm::Signed128(amount), VmTerm::Unsigned32(_))
                        if amount == block_reward =>
                    {
                        let result = script.execute(
                            &self.script_args,
                            input_stack,
                            to_add,
                            outs_sum,
                            coloured_ins_sums,
                            coloured_outs_sums,
                            idx_map,
                            ver_stack,
                            [0; 32],
                            key,
                            SETTINGS.node.network_name.as_str(),
                            VmFlags {
                                is_coinbase: true,
                                chain_id,
                                chain_height: height,
                                chain_timestamp: timestamp,
                                build_stacktrace: false,
                                validate_output_amounts: true,
                                prev_block_hash: prev_block_hash.0,
                                in_binary: self.to_bytes_for_signing(),
                                spent_out: None,
                                can_fail: false,
                                ..Default::default()
                            },
                        );

                        // Validate script execution
                        match result {
                            VmResult(Ok(ExecutionResult::Ok)) => {
                                *ins_sum += block_reward;
                                Ok(())
                            }
                            _ => Err(TxVerifyErr::InvalidScriptExecution),
                        }
                    }
                    _ => Err(TxVerifyErr::InvalidCoinbaseArgs),
                }
            }

            InputFlags::IsCoinbaseWithoutSpendKey => {
                if !coinbase_allowed {
                    return Err(TxVerifyErr::CoinbaseNotAllowed);
                }

                let script = Script::new_coinbase();

                let a1 = &self.script_args[0];
                let a3 = &self.script_args[2];

                // Validate terms
                match (a1, a3) {
                    (VmTerm::Signed128(amount), VmTerm::Unsigned32(_))
                        if amount == block_reward =>
                    {
                        let mut script_args = self.script_args.clone();
                        // Push a zero address at index 1
                        script_args.insert(1, VmTerm::Hash160([0; 20]));
                        let result = script.execute(
                            &script_args,
                            input_stack,
                            to_add,
                            outs_sum,
                            coloured_ins_sums,
                            coloured_outs_sums,
                            idx_map,
                            ver_stack,
                            [0; 32],
                            key,
                            SETTINGS.node.network_name.as_str(),
                            VmFlags {
                                is_coinbase: true,
                                chain_id,
                                chain_height: height,
                                chain_timestamp: timestamp,
                                build_stacktrace: false,
                                validate_output_amounts: true,
                                prev_block_hash: prev_block_hash.0,
                                in_binary: self.to_bytes_for_signing(),
                                spent_out: None,
                                can_fail: false,
                                ..Default::default()
                            },
                        );

                        // Validate script execution
                        match result {
                            VmResult(Ok(ExecutionResult::Ok)) => {
                                *ins_sum += block_reward;
                                Ok(())
                            }
                            _ => Err(TxVerifyErr::InvalidScriptExecution),
                        }
                    }
                    _ => Err(TxVerifyErr::InvalidCoinbaseArgs),
                }
            }

            InputFlags::IsColouredCoinbase => {
                let coloured_coinbase_block_height = self.coloured_coinbase_block_height.unwrap();

                // Check that the block height is between current and the horizon
                if coloured_coinbase_block_height >= height
                    || coloured_coinbase_block_height
                        < height.checked_sub(BLOCK_HORIZON).unwrap_or(0)
                {
                    return Err(TxVerifyErr::InvalidColouredCoinbaseBlockHeight);
                }

                validate_coloured_coinbase_idempotency(&self)?;

                // Compute colour hash which is the hash of the script + non malleable script args + spending key
                let mut bytes = self.script.to_bytes();
                let mut copied_args = self.script_args.clone();
                let mut i = 0;
                let mut r = 0;
                while i + r < self.script.malleable_args.len() {
                    if self.script.malleable_args[i + r] {
                        copied_args.remove(i);
                        r += 1;
                    } else {
                        i += 1;
                    }
                }
                for a in copied_args {
                    bytes.extend_from_slice(&a.to_bytes());
                }
                bytes.extend_from_slice(&self.spending_pkey.as_ref().unwrap().to_bytes());
                let colour_hash = Hash160::hash_from_slice(bytes, COLOUR_HASH_KEY);

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        [0; 32], // Empty seed, not failable
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: true,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            colour_hash: Some(colour_hash),
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: None,
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                Ok(())
            }

            InputFlags::Plain => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let address_to_check = self.spending_pkey.as_ref().unwrap().to_address();

                // Verify address
                if &address_to_check != out.address.as_ref().unwrap() {
                    return Err(TxVerifyErr::InvalidPublicKey);
                }

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        [0; 32], // Empty seed, not failable
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::FailablePlain => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let address_to_check = self.spending_pkey.as_ref().unwrap().to_address();

                // Verify address
                if &address_to_check != out.address.as_ref().unwrap() {
                    return Err(TxVerifyErr::InvalidPublicKey);
                }

                let seed_hash = Hash256::hash_from_slice(seed_bytes, key);

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        seed_hash.0,
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::PlainWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(&out.script_hash) {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        [0; 32], // Empty seed, not failable
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::FailablePlainWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(&out.script_hash) {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let seed_hash = Hash256::hash_from_slice(seed_bytes, key);

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        seed_hash.0,
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::IsColoured => {
                let out = self.out.as_ref().unwrap();
                unimplemented!()
            }

            InputFlags::HasSpendProof => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
                lemma.push(out.script_hash.clone());
                let merkle_proof = Proof::<Hash160>::new::<U2, U2>(
                    None,
                    lemma,
                    spend_proof
                        .1
                        .iter()
                        .map(|p| *p as usize)
                        .collect::<Vec<_>>(),
                )
                .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                let address_to_check = self.spending_pkey.as_ref().unwrap().to_address();
                let script_hash = self.script.to_script_hash(key);
                let mpr = merkle_proof
                    .validate_with_data::<Hash160Algo>(&<(Address, Hash160) as Into<
                        AddressAndHash160,
                    >>::into((
                        address_to_check,
                        script_hash,
                    )))
                    .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                if !mpr {
                    return Err(TxVerifyErr::InvalidSpendProof);
                }

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        [0; 32],
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::FailableHasSpendProof => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
                lemma.push(out.script_hash.clone());
                let merkle_proof = Proof::<Hash160>::new::<U2, U2>(
                    None,
                    lemma,
                    spend_proof
                        .1
                        .iter()
                        .map(|p| *p as usize)
                        .collect::<Vec<_>>(),
                )
                .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                let address_to_check = self.spending_pkey.as_ref().unwrap().to_address();
                let script_hash = self.script.to_script_hash(key);
                let mpr = merkle_proof
                    .validate_with_data::<Hash160Algo>(&<(Address, Hash160) as Into<
                        AddressAndHash160,
                    >>::into((
                        address_to_check,
                        script_hash,
                    )))
                    .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                if !mpr {
                    return Err(TxVerifyErr::InvalidSpendProof);
                }

                let seed_hash = Hash256::hash_from_slice(seed_bytes, key);

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        seed_hash.0,
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::HasSpendProofWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(&out.script_hash) {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
                lemma.push(out.script_hash.clone());
                let merkle_proof = Proof::<Hash160>::new::<U2, U2>(
                    None,
                    lemma,
                    spend_proof
                        .1
                        .iter()
                        .map(|p| *p as usize)
                        .collect::<Vec<_>>(),
                )
                .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                let script_hash = self.script.to_script_hash(key);
                let mpr = merkle_proof
                    .validate_with_data::<Hash160Algo>(&script_hash)
                    .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                if !mpr {
                    return Err(TxVerifyErr::InvalidSpendProof);
                }

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        [0; 32],
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::FailableHasSpendProofWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(&out.script_hash) {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                // Validate coinbase height against block horizon as coinbase outputs
                // can only be spent if they are created beyong the block horizon.
                if out.is_coinbase() {
                    let out_height = out.coinbase_height().unwrap();

                    if height < out_height + BLOCK_HORIZON {
                        return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
                    }
                }

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
                lemma.push(out.script_hash.clone());
                let merkle_proof = Proof::<Hash160>::new::<U2, U2>(
                    None,
                    lemma,
                    spend_proof
                        .1
                        .iter()
                        .map(|p| *p as usize)
                        .collect::<Vec<_>>(),
                )
                .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                let script_hash = self.script.to_script_hash(key);
                let mpr = merkle_proof
                    .validate_with_data::<Hash160Algo>(&script_hash)
                    .map_err(|_| TxVerifyErr::InvalidSpendProof)?;
                if !mpr {
                    return Err(TxVerifyErr::InvalidSpendProof);
                }

                let seed_hash = Hash256::hash_from_slice(seed_bytes, key);

                let result = self
                    .script
                    .execute(
                        &self.script_args,
                        input_stack,
                        to_add,
                        outs_sum,
                        coloured_ins_sums,
                        coloured_outs_sums,
                        idx_map,
                        ver_stack,
                        seed_hash.0,
                        key,
                        SETTINGS.node.network_name.as_str(),
                        VmFlags {
                            is_coinbase: false,
                            chain_id,
                            chain_height: height,
                            chain_timestamp: timestamp,
                            build_stacktrace: false,
                            validate_output_amounts: true,
                            prev_block_hash: prev_block_hash.0,
                            in_binary: self.to_bytes_for_signing(),
                            spent_out: Some(out.clone()),
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            _ => unimplemented!(),
        }
    }
}

impl Encode for Input {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        let flags = self.input_flags;
        let flags_to_write: u8 = flags as u8;
        bincode::Encode::encode(&flags_to_write, encoder)?;

        match flags {
            InputFlags::IsCoinbase => {
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::IsCoinbaseWithoutSpendKey => {
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::IsColouredCoinbase | InputFlags::FailableIsColouredCoinbase => {
                bincode::Encode::encode(self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::IsColouredCoinbaseWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseWithoutSpendKey => {
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::IsColouredCoinbaseHasColourProof
            | InputFlags::FailableIsColouredCoinbaseHasColourProof => {
                bincode::Encode::encode(self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseHasColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasColourProofWithoutSpendKey => {
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseHasSpendProof
            | InputFlags::FailableIsColouredCoinbaseHasSpendProof => {
                bincode::Encode::encode(self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofWithoutSpendKey => {
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseHasSpendProofAndColourProof
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProof => {
                bincode::Encode::encode(self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey => {
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.coloured_coinbase_nonce.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::Plain | InputFlags::FailablePlain => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.witness.as_ref().unwrap().to_bytes(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::PlainWithoutSpendKey | InputFlags::FailablePlainWithoutSpendKey => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::HasSpendProof | InputFlags::FailableHasSpendProof => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::HasSpendProofWithoutSpendKey
            | InputFlags::FailableHasSpendProofWithoutSpendKey => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColoured | InputFlags::FailableIsColoured => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredHasSpendProof | InputFlags::FailableIsColouredHasSpendProof => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredHasSpendProofAndColourProof
            | InputFlags::FailableIsColouredHasSpendProofAndColourProof => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredWithoutSpendKey
            | InputFlags::FailableIsColouredWithoutSpendKey => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredHasColourProof | InputFlags::FailableIsColouredHasColourProof => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredHasColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasColourProofWithoutSpendKey => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofWithoutSpendKey => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofAndColourProofWithoutSpendKey => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.colour_proof.as_ref().unwrap(), encoder)?;
            }
        }

        Ok(())
    }
}

impl Decode for Input {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let input_flags: u8 = bincode::Decode::decode(decoder)?;
        let input_flags: InputFlags = input_flags.try_into().map_err(|err: &'static str| {
            bincode::error::DecodeError::OtherString(err.to_owned())
        })?;

        match input_flags {
            InputFlags::IsCoinbase => {
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;

                // Validate number of coinbase arguments
                if script_args.len() != 4 {
                    return Err(bincode::error::DecodeError::OtherString(
                        format!(
                            "invalid argument length for coinbase! expected 5, found {}",
                            script_args.len()
                        )
                        .to_owned(),
                    ));
                }

                Ok(Self {
                    script_args,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsCoinbaseWithoutSpendKey => {
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;

                // Validate number of coinbase arguments
                if script_args.len() != 3 {
                    return Err(bincode::error::DecodeError::OtherString(
                        format!(
                            "invalid argument length for coinbase! expected 4, found {}",
                            script_args.len()
                        )
                        .to_owned(),
                    ));
                }

                Ok(Self {
                    script_args,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbase | InputFlags::FailableIsColouredCoinbase => {
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseWithoutSpendKey => {
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseHasColourProof
            | InputFlags::FailableIsColouredCoinbaseHasColourProof => {
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseHasColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasColourProofWithoutSpendKey => {
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseHasSpendProof
            | InputFlags::FailableIsColouredCoinbaseHasSpendProof => {
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let spend_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    spend_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofWithoutSpendKey => {
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let spend_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    spend_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseHasSpendProofAndColourProof
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProof => {
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let spend_proof = Some(bincode::Decode::decode(decoder)?);
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    spend_proof,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey => {
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_nonce = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let spend_proof = Some(bincode::Decode::decode(decoder)?);
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    spend_proof,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::Plain | InputFlags::FailablePlain => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    ..Default::default()
                })
            }

            InputFlags::PlainWithoutSpendKey | InputFlags::FailablePlainWithoutSpendKey => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    ..Default::default()
                })
            }

            InputFlags::HasSpendProof | InputFlags::FailableHasSpendProof => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let spend_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    spend_proof,
                    ..Default::default()
                })
            }

            InputFlags::HasSpendProofWithoutSpendKey
            | InputFlags::FailableHasSpendProofWithoutSpendKey => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let spend_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    witness,
                    out,
                    spend_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColoured | InputFlags::FailableIsColoured => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasSpendProof | InputFlags::FailableIsColouredHasSpendProof => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);
                let spend_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    spend_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasSpendProofAndColourProof
            | InputFlags::FailableIsColouredHasSpendProofAndColourProof => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);
                let spend_proof = Some(bincode::Decode::decode(decoder)?);
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    spend_proof,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredWithoutSpendKey
            | InputFlags::FailableIsColouredWithoutSpendKey => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasColourProof | InputFlags::FailableIsColouredHasColourProof => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasColourProofWithoutSpendKey => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    colour_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofWithoutSpendKey => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);
                let spend_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    spend_proof,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofAndColourProofWithoutSpendKey => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;
                let colour_script = bincode::Decode::decode(decoder)?;
                let colour_script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(
                    &colour_script,
                    colour_script_args.as_slice(),
                )?;
                let colour_script = Some(colour_script);
                let colour_script_args = Some(colour_script_args);
                let spend_proof = Some(bincode::Decode::decode(decoder)?);
                let colour_proof = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    witness,
                    out,
                    colour_script,
                    colour_script_args,
                    spend_proof,
                    colour_proof,
                    ..Default::default()
                })
            }
        }
    }
}

fn validate_script_args_len_during_decode(
    script: &Script,
    script_args: &[VmTerm],
) -> Result<(), bincode::error::DecodeError> {
    if script.malleable_args.len() != script_args.len() {
        return Err(bincode::error::DecodeError::OtherString(format!("Received more or fewer script arguments than the script requires. Expected: {}, Found: {}", script.malleable_args.len(), script_args.len())));
    }

    Ok(())
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum InputFlags {
    IsCoinbase = 0x00,
    IsColouredCoinbase = 0x01,
    Plain = 0x02,
    HasSpendProof = 0x03,
    IsColoured = 0x04,
    IsColouredHasColourProof = 0x05,
    IsColouredHasSpendProof = 0x06,
    IsColouredHasSpendProofAndColourProof = 0x07,
    HasSpendProofWithoutSpendKey = 0x08,
    IsColouredWithoutSpendKey = 0x09,
    IsColouredHasColourProofWithoutSpendKey = 0x0a,
    IsColouredHasSpendProofWithoutSpendKey = 0x0b,
    IsColouredHasSpendProofAndColourProofWithoutSpendKey = 0x0c,
    IsCoinbaseWithoutSpendKey = 0x0d,
    FailablePlain = 0x0e,
    FailableHasSpendProof = 0x0f,
    FailableIsColoured = 0x10,
    FailableIsColouredHasColourProof = 0x11,
    FailableIsColouredHasSpendProof = 0x12,
    FailableIsColouredHasSpendProofAndColourProof = 0x13,
    FailableHasSpendProofWithoutSpendKey = 0x14,
    FailableIsColouredWithoutSpendKey = 0x15,
    FailableIsColouredHasColourProofWithoutSpendKey = 0x16,
    FailableIsColouredHasSpendProofWithoutSpendKey = 0x17,
    FailableIsColouredHasSpendProofAndColourProofWithoutSpendKey = 0x18,
    IsColouredCoinbaseHasColourProof = 0x19,
    IsColouredCoinbaseHasSpendProof = 0x1a,
    IsColouredCoinbaseHasSpendProofAndColourProof = 0x1b,
    IsColouredCoinbaseWithoutSpendKey = 0x1c,
    IsColouredCoinbaseHasColourProofWithoutSpendKey = 0x1d,
    IsColouredCoinbaseHasSpendProofWithoutSpendKey = 0x1e,
    IsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey = 0x1f,
    FailableIsColouredCoinbase = 0x20,
    FailableIsColouredCoinbaseHasColourProof = 0x21,
    FailableIsColouredCoinbaseHasSpendProof = 0x22,
    FailableIsColouredCoinbaseHasSpendProofAndColourProof = 0x23,
    FailableIsColouredCoinbaseWithoutSpendKey = 0x24,
    FailableIsColouredCoinbaseHasColourProofWithoutSpendKey = 0x25,
    FailableIsColouredCoinbaseHasSpendProofWithoutSpendKey = 0x26,
    FailableIsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey = 0x27,
    PlainWithoutSpendKey = 0x28,
    FailablePlainWithoutSpendKey = 0x29,
}

impl std::convert::TryFrom<u8> for InputFlags {
    type Error = &'static str;

    fn try_from(num: u8) -> Result<Self, Self::Error> {
        match num {
            0x00 => Ok(Self::IsCoinbase),
            0x01 => Ok(Self::IsColouredCoinbase),
            0x02 => Ok(Self::Plain),
            0x03 => Ok(Self::HasSpendProof),
            0x04 => Ok(Self::IsColoured),
            0x05 => Ok(Self::IsColouredHasColourProof),
            0x06 => Ok(Self::IsColouredHasSpendProof),
            0x07 => Ok(Self::IsColouredHasSpendProofAndColourProof),
            0x08 => Ok(Self::HasSpendProofWithoutSpendKey),
            0x09 => Ok(Self::IsColouredWithoutSpendKey),
            0x0a => Ok(Self::IsColouredHasColourProofWithoutSpendKey),
            0x0b => Ok(Self::IsColouredHasSpendProofWithoutSpendKey),
            0x0c => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutSpendKey),
            0x0d => Ok(Self::IsCoinbaseWithoutSpendKey),
            0x0e => Ok(Self::FailablePlain),
            0x0f => Ok(Self::FailableHasSpendProof),
            0x10 => Ok(Self::FailableIsColoured),
            0x11 => Ok(Self::FailableIsColouredHasColourProof),
            0x12 => Ok(Self::FailableIsColouredHasSpendProof),
            0x13 => Ok(Self::FailableIsColouredHasSpendProofAndColourProof),
            0x14 => Ok(Self::FailableHasSpendProofWithoutSpendKey),
            0x15 => Ok(Self::FailableIsColouredWithoutSpendKey),
            0x16 => Ok(Self::FailableIsColouredHasColourProofWithoutSpendKey),
            0x17 => Ok(Self::FailableIsColouredHasSpendProofWithoutSpendKey),
            0x18 => Ok(Self::FailableIsColouredHasSpendProofAndColourProofWithoutSpendKey),
            0x19 => Ok(Self::IsColouredCoinbaseHasColourProof),
            0x1a => Ok(Self::IsColouredCoinbaseHasSpendProof),
            0x1b => Ok(Self::IsColouredCoinbaseHasSpendProofAndColourProof),
            0x1c => Ok(Self::IsColouredCoinbaseWithoutSpendKey),
            0x1d => Ok(Self::IsColouredCoinbaseHasColourProofWithoutSpendKey),
            0x1e => Ok(Self::IsColouredCoinbaseHasSpendProofWithoutSpendKey),
            0x1f => Ok(Self::IsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey),
            0x20 => Ok(Self::FailableIsColouredCoinbase),
            0x21 => Ok(Self::FailableIsColouredCoinbaseHasColourProof),
            0x22 => Ok(Self::FailableIsColouredCoinbaseHasSpendProof),
            0x23 => Ok(Self::FailableIsColouredCoinbaseHasSpendProofAndColourProof),
            0x24 => Ok(Self::FailableIsColouredCoinbaseWithoutSpendKey),
            0x25 => Ok(Self::FailableIsColouredCoinbaseHasColourProofWithoutSpendKey),
            0x26 => Ok(Self::FailableIsColouredCoinbaseHasSpendProofWithoutSpendKey),
            0x27 => Ok(Self::FailableIsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey),
            0x28 => Ok(Self::PlainWithoutSpendKey),
            0x29 => Ok(Self::FailablePlainWithoutSpendKey),
            _ => Err("invalid bitflags"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::Address;

    #[test]
    fn coinbase_encode_decode() {
        let input = Input {
            input_flags: InputFlags::IsCoinbase,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coinbase_without_spend_key_encode_decode() {
        let input = Input {
            input_flags: InputFlags::IsCoinbaseWithoutSpendKey,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbase,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbase,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseWithoutSpendKey,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbaseWithoutSpendKey,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_has_colour_proof_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseHasColourProof,
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_has_colour_proof_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbaseHasColourProof,
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_has_colour_proof_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseHasColourProofWithoutSpendKey,
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_has_colour_proof_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbaseHasColourProofWithoutSpendKey,
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_has_spend_proof_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseHasSpendProof,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_has_spend_proof_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbaseHasSpendProof,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_has_spend_proof_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseHasSpendProofWithoutSpendKey,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_has_spend_proof_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbaseHasSpendProofWithoutSpendKey,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_has_spend_proof_and_colour_proof_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseHasSpendProofAndColourProof,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_has_spend_proof_and_colour_proof_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProof,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_has_spend_proof_and_colour_proof_without_spend_key_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags: InputFlags::IsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn failable_coloured_coinbase_has_spend_proof_and_colour_proof_without_spend_key_encode_decode()
    {
        let input = Input {
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            coloured_coinbase_nonce: Some(0),
            input_flags:
                InputFlags::FailableIsColouredCoinbaseHasSpendProofAndColourProofWithoutSpendKey,
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn plain_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::Plain,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn has_spend_proof_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::HasSpendProof,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn has_spend_proof_without_spend_key_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::HasSpendProofWithoutSpendKey,
            script: Script::new_simple_spend(),
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColoured,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_has_spend_proof_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredHasSpendProof,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_has_spend_proof_and_colour_proof_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredHasSpendProofAndColourProof,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_without_spend_key_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredWithoutSpendKey,
            script: Script::new_simple_spend(),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_has_colour_proof_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredHasColourProof,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_has_spend_proof_and_colour_proof_without_spend_key_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredHasSpendProofAndColourProofWithoutSpendKey,
            script: Script::new_simple_spend(),
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_has_spend_proof_without_spend_key_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredHasSpendProofWithoutSpendKey,
            script: Script::new_simple_spend(),
            spend_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_has_colour_proof_without_spend_key_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::IsColouredHasColourProofWithoutSpendKey,
            script: Script::new_simple_spend(),
            colour_proof: Some((
                vec![Hash160::zero(), Hash160::zero(), Hash160::zero()],
                vec![0, 0, 0],
            )),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            colour_script: Some(Script::new_simple_spend()),
            colour_script_args: Some(vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ]),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }
}
