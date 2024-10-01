// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{Shard, ShardBackend};
use crate::consensus::{Money, BLOCK_HORIZON};
use crate::primitives::{
    compute_colour_hash, get_non_malleable_script_args, Address, AddressAndHash160, Hash160,
    Hash160Algo, Hash256, OutWitnessVec, Output, PublicKey, TxVerifyErr, COLOUR_HASH_KEY,
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

use super::validate_script_against_colour_hash;

const INVALID_OUT_ERR_TEXT: &str = "Invalid output type for these input flags";

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

    /// The colour kernel of a coloured input. This must be present to validate the colour script hash
    /// against the colour hash.
    pub colour_kernel: Option<Hash160>,

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
            coloured_coinbase_block_height: None,
            coloured_coinbase_nonce: None,
            colour_kernel: None,
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
            | InputFlags::FailableIsColouredHasSpendProof
            | InputFlags::FailableHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredCoinbase => true,
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
                    || coloured_coinbase_block_height < height.saturating_sub(BLOCK_HORIZON)
                {
                    return Err(TxVerifyErr::InvalidColouredCoinbaseBlockHeight);
                }

                validate_coloured_coinbase_idempotency(self)?;
                let nmsa =
                    get_non_malleable_script_args(&self.script_args, &self.script.malleable_args)
                        .unwrap();
                let colour_hash =
                    compute_colour_hash(&self.script, &nmsa, self.spending_pkey.as_ref().unwrap())
                        .0;

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

            InputFlags::FailableIsColouredCoinbase => {
                let coloured_coinbase_block_height = self.coloured_coinbase_block_height.unwrap();

                // Check that the block height is between current and the horizon
                if coloured_coinbase_block_height >= height
                    || coloured_coinbase_block_height < height.saturating_sub(BLOCK_HORIZON)
                {
                    return Err(TxVerifyErr::InvalidColouredCoinbaseBlockHeight);
                }

                validate_coloured_coinbase_idempotency(self)?;
                let nmsa =
                    get_non_malleable_script_args(&self.script_args, &self.script.malleable_args)
                        .unwrap();
                let colour_hash =
                    compute_colour_hash(&self.script, &nmsa, self.spending_pkey.as_ref().unwrap())
                        .0;
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
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                Ok(())
            }

            InputFlags::IsColouredCoinbaseWithoutSpendKey => {
                let coloured_coinbase_block_height = self.coloured_coinbase_block_height.unwrap();

                // Check that the block height is between current and the horizon
                if coloured_coinbase_block_height >= height
                    || coloured_coinbase_block_height < height.saturating_sub(BLOCK_HORIZON)
                {
                    return Err(TxVerifyErr::InvalidColouredCoinbaseBlockHeight);
                }

                validate_coloured_coinbase_idempotency(self)?;
                let nmsa =
                    get_non_malleable_script_args(&self.script_args, &self.script.malleable_args)
                        .unwrap();
                let colour_hash =
                    compute_colour_hash(&self.script, &nmsa, self.spending_pkey.as_ref().unwrap())
                        .0;

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

            InputFlags::FailableIsColouredCoinbaseWithoutSpendKey => {
                let coloured_coinbase_block_height = self.coloured_coinbase_block_height.unwrap();

                // Check that the block height is between current and the horizon
                if coloured_coinbase_block_height >= height
                    || coloured_coinbase_block_height < height.saturating_sub(BLOCK_HORIZON)
                {
                    return Err(TxVerifyErr::InvalidColouredCoinbaseBlockHeight);
                }

                validate_coloured_coinbase_idempotency(self)?;
                let nmsa =
                    get_non_malleable_script_args(&self.script_args, &self.script.malleable_args)
                        .unwrap();
                let colour_hash =
                    compute_colour_hash(&self.script, &nmsa, self.spending_pkey.as_ref().unwrap())
                        .0;
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
                            can_fail: true,
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

            InputFlags::FailableIsColoured => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(
                    &(
                        &out.coloured_address.as_ref().unwrap().to_address(),
                        &out.script_hash,
                    )
                        .into(),
                ) {
                    to_add[*idx as usize].clone()
                } else {
                    to_delete.push((
                        self.out.as_ref().unwrap().clone(),
                        self.witness.as_ref().unwrap().clone(),
                    ));
                    out.clone()
                };
                let out_amount = out.amount;
                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let coloured_address = out
                    .coloured_address
                    .as_ref()
                    .ok_or(TxVerifyErr::InvalidOutput)?;

                let colour_hash = coloured_address.colour_hash();
                let address_to_check = self
                    .spending_pkey
                    .as_ref()
                    .unwrap()
                    .to_coloured_address(&colour_hash);

                // Verify address
                if &address_to_check != coloured_address {
                    return Err(TxVerifyErr::InvalidPublicKey);
                }

                // Verify colour script
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }
                let seed_hash = Hash256::hash_from_slice(seed_bytes, key);

                self.script
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
                            colour_hash: Some(colour_hash.clone()),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
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
                            is_colour_script: true,
                            colour_hash: Some(colour_hash.clone()),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                // Add amount to sums
                if let Some(ins_sum) = coloured_ins_sums.get_mut(&colour_hash) {
                    *ins_sum += out_amount;
                } else {
                    coloured_ins_sums.insert(colour_hash, out_amount);
                }

                Ok(())
            }

            InputFlags::IsColoured => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(
                    &(
                        &out.coloured_address.as_ref().unwrap().to_address(),
                        &out.script_hash,
                    )
                        .into(),
                ) {
                    to_add[*idx as usize].clone()
                } else {
                    to_delete.push((
                        self.out.as_ref().unwrap().clone(),
                        self.witness.as_ref().unwrap().clone(),
                    ));
                    out.clone()
                };
                let out_amount = out.amount;
                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let coloured_address = out
                    .coloured_address
                    .as_ref()
                    .ok_or(TxVerifyErr::InvalidOutput)?;

                let colour_hash = coloured_address.colour_hash();
                let address_to_check = self
                    .spending_pkey
                    .as_ref()
                    .unwrap()
                    .to_coloured_address(&colour_hash);

                // Verify address
                if &address_to_check != coloured_address {
                    return Err(TxVerifyErr::InvalidPublicKey);
                }

                // Verify colour script
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }

                self.script
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
                            colour_hash: Some(colour_hash.clone()),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
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
                            spent_out: Some(out),
                            can_fail: false,
                            is_colour_script: true,
                            colour_hash: Some(colour_hash.clone()),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                // Add amount to sums
                if let Some(ins_sum) = coloured_ins_sums.get_mut(&colour_hash) {
                    *ins_sum += out_amount;
                } else {
                    coloured_ins_sums.insert(colour_hash, out_amount);
                }

                Ok(())
            }

            InputFlags::IsColouredWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let out = if let Some(idx) = idx_map.get(
                    &(
                        &out.coloured_address.as_ref().unwrap().to_address(),
                        &out.script_hash,
                    )
                        .into(),
                ) {
                    to_add[*idx as usize].clone()
                } else {
                    to_delete.push((
                        self.out.as_ref().unwrap().clone(),
                        self.witness.as_ref().unwrap().clone(),
                    ));
                    out.clone()
                };
                let coloured_address = out.coloured_address.as_ref().unwrap();
                let out_amount = out.amount;
                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let colour_hash = coloured_address.colour_hash();

                // Verify colour script hash
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }

                self.script
                    .execute(
                        &self.script_args,
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash.clone()),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
                        input_stack,
                        &mut to_add_buf,
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
                            is_colour_script: true,
                            colour_hash: Some(colour_hash),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                // Add amount to sums
                if let Some(ins_sum) = coloured_ins_sums.get_mut(&colour_hash) {
                    *ins_sum += out_amount;
                } else {
                    coloured_ins_sums.insert(colour_hash, out_amount);
                }

                Ok(())
            }

            InputFlags::FailableIsColouredWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let mut to_add_buf = vec![];
                let coloured_address = out.coloured_address.as_ref().unwrap();
                let address = coloured_address.to_address();
                let out = if let Some(idx) = idx_map.get(&(&address, &out.script_hash).into()) {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;
                let script_hash = self.script.to_script_hash(key);

                // Verify script hash
                if script_hash != out.script_hash {
                    return Err(TxVerifyErr::InvalidScriptHash);
                }

                let colour_hash = coloured_address.colour_hash();

                // Verify colour script hash
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }
                let seed_hash = Hash256::hash_from_slice(seed_bytes, key);

                self.script
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
                            can_fail: false,
                            colour_hash: Some(colour_hash.clone()),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
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
                            is_colour_script: true,
                            colour_hash: Some(colour_hash),
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                to_add.extend(to_add_buf);
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::IsColouredHasSpendProof => {
                let out = self.out.as_ref().unwrap();
                let mut to_add_buf = vec![];
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                let coloured_address = out
                    .coloured_address
                    .as_ref()
                    .ok_or(TxVerifyErr::InvalidOutput)?;
                let colour_hash = coloured_address.colour_hash();

                // Verify colour script hash
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }

                let address_to_check = self
                    .spending_pkey
                    .as_ref()
                    .unwrap()
                    .to_coloured_address(&colour_hash)
                    .to_address();

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
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

                self.script
                    .execute(
                        &self.script_args,
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash.clone()),
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash),
                            is_colour_script: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                to_add.extend(to_add_buf);
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::FailableIsColouredHasSpendProof => {
                let out = self.out.as_ref().unwrap();
                let mut to_add_buf = vec![];
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                let coloured_address = out
                    .coloured_address
                    .as_ref()
                    .ok_or(TxVerifyErr::InvalidOutput)?;
                let colour_hash = coloured_address.colour_hash();

                // Verify colour script hash
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }

                let address_to_check = self
                    .spending_pkey
                    .as_ref()
                    .unwrap()
                    .to_coloured_address(&colour_hash)
                    .to_address();

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
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

                self.script
                    .execute(
                        &self.script_args,
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash.clone()),
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash),
                            can_fail: true,
                            is_colour_script: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                to_add.extend(to_add_buf);
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::IsColouredHasSpendProofWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let mut to_add_buf = vec![];
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                let coloured_address = out
                    .coloured_address
                    .as_ref()
                    .ok_or(TxVerifyErr::InvalidOutput)?;
                let colour_hash = coloured_address.colour_hash();

                // Verify colour script hash
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
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

                self.script
                    .execute(
                        &self.script_args,
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash.clone()),
                            can_fail: false,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash),
                            is_colour_script: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                to_add.extend(to_add_buf);
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
            }

            InputFlags::FailableIsColouredHasSpendProofWithoutSpendKey => {
                let out = self.out.as_ref().unwrap();
                let mut to_add_buf = vec![];
                let out = if let Some(idx) =
                    idx_map.get(&(out.address.as_ref().unwrap(), &out.script_hash).into())
                {
                    &to_add[*idx as usize]
                } else {
                    out
                };
                let out_amount = out.amount;

                let coloured_address = out
                    .coloured_address
                    .as_ref()
                    .ok_or(TxVerifyErr::InvalidOutput)?;
                let colour_hash = coloured_address.colour_hash();

                // Verify colour script hash
                if !validate_script_against_colour_hash(
                    self.colour_script.as_ref().unwrap(),
                    &colour_hash,
                    self.colour_kernel.as_ref().unwrap(),
                ) {
                    return Err(TxVerifyErr::InvalidColourScriptHash);
                }

                // Verify spend proof
                let spend_proof = self.spend_proof.as_ref().unwrap();
                let mut lemma = spend_proof.0.clone();
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

                self.script
                    .execute(
                        &self.script_args,
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash.clone()),
                            can_fail: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                self.colour_script
                    .as_ref()
                    .unwrap()
                    .execute(
                        self.colour_script_args.as_ref().unwrap(),
                        input_stack,
                        &mut to_add_buf,
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
                            colour_hash: Some(colour_hash),
                            is_colour_script: true,
                            ..Default::default()
                        },
                    )
                    .0
                    .map_err(|_| TxVerifyErr::InvalidScriptExecution)?;

                to_add.extend(to_add_buf);
                *ins_sum += out_amount;
                to_delete.push((
                    self.out.as_ref().unwrap().clone(),
                    self.witness.as_ref().unwrap().clone(),
                ));
                Ok(())
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

            InputFlags::Plain | InputFlags::FailablePlain => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                if let Some(witness) = self.witness.as_ref() {
                    bincode::Encode::encode(&witness.to_bytes(), encoder)?;
                }
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
                bincode::Encode::encode(&self.colour_kernel.as_ref().unwrap(), encoder)?;
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
                bincode::Encode::encode(&self.colour_kernel.as_ref().unwrap(), encoder)?;
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
                bincode::Encode::encode(&self.colour_kernel.as_ref().unwrap(), encoder)?;
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
                bincode::Encode::encode(&self.colour_kernel.as_ref().unwrap(), encoder)?;
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
                    spending_pkey,
                    script,
                    script_args,
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    input_flags,
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
                    coloured_coinbase_block_height,
                    coloured_coinbase_nonce,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::Plain | InputFlags::FailablePlain => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                    out,
                    spending_pkey,
                    witness,
                    script,
                    script_args,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::PlainWithoutSpendKey | InputFlags::FailablePlainWithoutSpendKey => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                    out,
                    spending_pkey,
                    witness,
                    script,
                    script_args,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::HasSpendProof | InputFlags::FailableHasSpendProof => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                    out,
                    spending_pkey,
                    witness,
                    script,
                    script_args,
                    spend_proof,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::HasSpendProofWithoutSpendKey
            | InputFlags::FailableHasSpendProofWithoutSpendKey => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                    out,
                    witness,
                    script,
                    script_args,
                    spend_proof,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsColoured | InputFlags::FailableIsColoured => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if !out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                let colour_kernel = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    out,
                    spending_pkey,
                    witness,
                    script,
                    colour_script,
                    script_args,
                    colour_script_args,
                    colour_kernel,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasSpendProof | InputFlags::FailableIsColouredHasSpendProof => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if !out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                let colour_kernel = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    out,
                    spending_pkey,
                    witness,
                    script,
                    colour_script,
                    script_args,
                    colour_script_args,
                    spend_proof,
                    colour_kernel,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredWithoutSpendKey
            | InputFlags::FailableIsColouredWithoutSpendKey => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if !out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                let colour_kernel = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    out,
                    witness,
                    script,
                    colour_script,
                    script_args,
                    colour_script_args,
                    colour_kernel,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredHasSpendProofWithoutSpendKey
            | InputFlags::FailableIsColouredHasSpendProofWithoutSpendKey => {
                let out: Output = bincode::Decode::decode(decoder)?;
                if !out.is_coloured() {
                    return Err(bincode::error::DecodeError::OtherString(
                        INVALID_OUT_ERR_TEXT.to_owned(),
                    ));
                }
                let out = Some(out);
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
                let colour_kernel = Some(bincode::Decode::decode(decoder)?);

                Ok(Self {
                    out,
                    witness,
                    script,
                    colour_script,
                    script_args,
                    colour_script_args,
                    spend_proof,
                    colour_kernel,
                    input_flags,
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
    IsColouredHasSpendProof = 0x05,
    HasSpendProofWithoutSpendKey = 0x06,
    IsColouredWithoutSpendKey = 0x07,
    IsColouredHasSpendProofWithoutSpendKey = 0x08,
    IsCoinbaseWithoutSpendKey = 0x09,
    FailablePlain = 0x0a,
    FailableHasSpendProof = 0x0b,
    FailableIsColoured = 0x0c,
    FailableIsColouredHasSpendProof = 0x0d,
    FailableHasSpendProofWithoutSpendKey = 0x0e,
    FailableIsColouredWithoutSpendKey = 0x0f,
    FailableIsColouredHasSpendProofWithoutSpendKey = 0x10,
    IsColouredCoinbaseWithoutSpendKey = 0x11,
    FailableIsColouredCoinbase = 0x12,
    FailableIsColouredCoinbaseWithoutSpendKey = 0x13,
    PlainWithoutSpendKey = 0x14,
    FailablePlainWithoutSpendKey = 0x15,
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
            0x05 => Ok(Self::IsColouredHasSpendProof),
            0x06 => Ok(Self::HasSpendProofWithoutSpendKey),
            0x07 => Ok(Self::IsColouredWithoutSpendKey),
            0x08 => Ok(Self::IsColouredHasSpendProofWithoutSpendKey),
            0x09 => Ok(Self::IsCoinbaseWithoutSpendKey),
            0x0a => Ok(Self::FailablePlain),
            0x0b => Ok(Self::FailableHasSpendProof),
            0x0c => Ok(Self::FailableIsColoured),
            0x0d => Ok(Self::FailableIsColouredHasSpendProof),
            0x0e => Ok(Self::FailableHasSpendProofWithoutSpendKey),
            0x0f => Ok(Self::FailableIsColouredWithoutSpendKey),
            0x10 => Ok(Self::FailableIsColouredHasSpendProofWithoutSpendKey),
            0x11 => Ok(Self::IsColouredCoinbaseWithoutSpendKey),
            0x12 => Ok(Self::FailableIsColouredCoinbase),
            0x13 => Ok(Self::FailableIsColouredCoinbaseWithoutSpendKey),
            0x14 => Ok(Self::PlainWithoutSpendKey),
            0x15 => Ok(Self::FailablePlainWithoutSpendKey),
            _ => Err("invalid bitflags"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::{Address, ColouredAddress};

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
    fn plain_fails_decoding_with_a_coloured_output() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
    }

    #[test]
    fn has_spend_proof_fails_decoding_with_a_coloured_output() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
    }

    #[test]
    fn has_spend_proof_without_spend_key_fails_decoding_with_a_coloured_output() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
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
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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
            colour_kernel: Some(Hash160::zero()),
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
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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
            colour_kernel: Some(Hash160::zero()),
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
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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
            colour_kernel: Some(Hash160::zero()),
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
                address: None,
                coloured_address: Some(ColouredAddress::zero()),
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
            colour_kernel: Some(Hash160::zero()),
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_fails_decode_on_non_coloured_output() {
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
            colour_kernel: Some(Hash160::zero()),
            ..Default::default()
        };

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
    }

    #[test]
    fn coloured_has_spend_proof_fails_decode_on_non_coloured_output() {
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
            colour_kernel: Some(Hash160::zero()),
            ..Default::default()
        };

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
    }

    #[test]
    fn coloured_without_spend_key_fails_decode_on_non_coloured_output() {
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
            colour_kernel: Some(Hash160::zero()),
            ..Default::default()
        };

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
    }

    #[test]
    fn coloured_has_spend_proof_without_spend_key_fails_decode_on_non_coloured_output() {
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
            colour_kernel: Some(Hash160::zero()),
            ..Default::default()
        };

        let decoded: Result<Input, _> =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap());
        assert_eq!(
            decoded,
            Err(bincode::error::DecodeError::OtherString(
                INVALID_OUT_ERR_TEXT.to_owned()
            ))
        );
    }
}
