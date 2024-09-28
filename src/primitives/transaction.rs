// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{Shard, ShardBackend};
use crate::consensus::{map_height_to_block_reward, Money};
use crate::primitives::{Address, Hash160, Hash256, Input, OutWitnessVec, Output};
use crate::settings::SETTINGS;
use crate::vm::{VerificationStack, VmFlags};
use bincode::{Decode, Encode};
use schnorrkel::{signing_context, verify_batch, PublicKey as SchnorPK, Signature as SchnorSig};
use std::cmp::Ordering;
use std::collections::HashMap;

#[derive(PartialEq, Debug, Clone)]
pub struct Transaction {
    pub chain_id: u8,
    pub ins: Vec<Input>,
    pub hash: Option<Hash256>,
}

impl Transaction {
    pub fn compute_hash(&mut self, key: &str) {
        let encoded = crate::codec::encode_to_vec(self).unwrap();
        self.hash = Some(Hash256::hash_from_slice(encoded, key));
    }

    /// Serialize to bytes
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    #[must_use]
    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    #[must_use]
    pub fn is_coinbase(&self) -> bool {
        if self.ins.len() != 1 {
            return false;
        }

        let input = &self.ins[0];
        input.is_coinbase()
    }

    #[must_use]
    pub fn get_ins(&self) -> &[Input] {
        &self.ins
    }

    /// Validate single transaction against the chain-state. Returns transaction fee if successful.
    /// Does not verify signatures.
    pub fn verify_single(
        &self,
        key: &str,
        height: u64,
        chain_id: u8,
        timestamp: i64,
        prev_block_hash: Hash256,
        block_reward: Money,
        coinbase_allowed: bool,
        to_add: &mut Vec<Output>,
        to_delete: &mut OutWitnessVec,
        ver_stack: &mut VerificationStack,
        idx_map: &mut HashMap<Hash160, u16>,
        tx_seed_bytes: &[u8],
        validate_coloured_coinbase: fn(&Input) -> Result<(), TxVerifyErr>,
    ) -> Result<Money, TxVerifyErr> {
        let mut ins_sum: Money = 0;
        let mut outs_sum: Money = 0;
        let mut coloured_ins_sums = HashMap::new();
        let mut coloured_outs_sums = HashMap::new();

        // Verify inputs
        for (i, input) in self.ins.iter().enumerate() {
            let nonce = (i as u64).to_le_bytes();
            let input_seed_bytes: &[u8] = &[tx_seed_bytes, nonce.as_slice()].concat();

            let result = input.verify(
                key,
                height,
                chain_id,
                &mut ins_sum,
                &mut outs_sum,
                &mut coloured_ins_sums,
                &mut coloured_outs_sums,
                timestamp,
                &block_reward,
                prev_block_hash,
                coinbase_allowed,
                to_add,
                to_delete,
                ver_stack,
                idx_map,
                input_seed_bytes,
                self.ins.as_slice(),
                validate_coloured_coinbase,
            );

            match (result, input.is_failable()) {
                (Err(err), false) => return Err(err), // Not failable so the whole transaction is invalid
                (Err(_), true) => break, // Stop the rest of the transaction execution at this point
                _ => {}
            }
        }

        // Check that the sum of inputs is greater than that of the outputs
        if ins_sum < outs_sum {
            return Err(TxVerifyErr::InvalidAmount);
        }

        // Verify coloured sums
        for (k, ins_sum) in coloured_ins_sums.iter() {
            let outs_sum = coloured_outs_sums.get(k).unwrap_or(&0);
            if ins_sum < outs_sum {
                return Err(TxVerifyErr::InvalidAmount);
            }
        }

        Ok(ins_sum - outs_sum)
    }
}

impl Encode for Transaction {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.chain_id, encoder)?;
        bincode::Encode::encode(&self.ins, encoder)?;
        Ok(())
    }
}

impl Decode for Transaction {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        Ok(Self {
            chain_id: bincode::Decode::decode(decoder)?,
            ins: bincode::Decode::decode(decoder)?,
            hash: None,
        })
    }
}

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum TxVerifyErr {
    InvalidAmount,
    InvalidSignature,
    FailedMoneyCheck,
    ZeroOutputAmount,
    CoinbaseOutSpentBeforeMaturation,
    CoinbaseNotAllowed,
    ColouredFeeNotAllowed,
    DuplicateCoinbase,
    DuplicateTxs,
    InvalidScriptHash,
    InvalidScriptExecution,
    InvalidCoinbase,
    InvalidCoinbaseArgs,
    InvalidSignaturesLength,
    InvalidPublicKey,
    InvalidSpendProof,
    InvalidColouredCoinbaseBlockHeight,
    InvalidInputType,
    InvalidOutput,
    InvalidColourScriptHash,
    BackendErr,
    Error(&'static str),
}

#[derive(Clone, Debug)]
/// Transaction with signatures used at the p2p layer for initial propagation.
pub struct TransactionWithSignatures {
    pub(crate) tx: Transaction,
    pub(crate) signatures: Vec<SchnorSig>,
}

impl TransactionWithSignatures {
    /// Verify only the signatures against the inputs in the transaction.
    pub fn verify_signatures(&self, key: &str) -> Result<(), TxVerifyErr> {
        let mut transcripts: Vec<Vec<u8>> = Vec::new();
        let mut public_keys: Vec<SchnorPK> = Vec::new();

        for input in &self.tx.ins {
            if let Some(pub_key) = &input.spending_pkey {
                let bytes = input.to_bytes_for_signing();
                transcripts.push(bytes);
                public_keys.push(pub_key.0.clone());
            }
        }

        if self.signatures.len() != public_keys.len() {
            return Err(TxVerifyErr::InvalidSignaturesLength);
        }

        let mut ctx = signing_context(key.as_bytes());

        // Verify all signatures against transcripts and public keys
        if verify_batch(
            transcripts.iter().map(|m| ctx.bytes(m.as_slice())),
            &self.signatures,
            &public_keys,
            false,
        )
        .is_err()
        {
            return Err(TxVerifyErr::InvalidSignature);
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
/// `TransactionWithFee` struct used for the mempool.
pub struct TransactionWithFee {
    pub(crate) tx: TransactionWithSignatures,
    pub(crate) raw_fee: Money,
    pub(crate) fee_per_byte: Money,
    pub(crate) tx_size: u32,
}

impl TransactionWithFee {
    #[must_use]
    pub fn hash(&self) -> Option<&Hash256> {
        self.tx.tx.hash()
    }

    #[must_use]
    pub fn from_transaction(
        other: TransactionWithSignatures,
        key: &str,
        height: u64,
        chain_id: u8,
        timestamp: i64,
        prev_block_hash: Hash256,
    ) -> Result<Self, TxVerifyErr> {
        let mut to_add = vec![];
        let mut to_delete = vec![];
        let mut ver_stack = VerificationStack::new();
        let mut idx_map = HashMap::new();
        let raw_fee = other.tx.verify_single(
            key,
            height,
            chain_id,
            timestamp,
            prev_block_hash,
            map_height_to_block_reward(height),
            false,
            &mut to_add,
            &mut to_delete,
            &mut ver_stack,
            &mut idx_map,
            &[0_u8; 32],
            |_| Ok(()),
        )?;
        let tx_size = other.tx.to_bytes().len() as u32;

        Ok(Self {
            tx: other,
            raw_fee,
            fee_per_byte: raw_fee / i128::from(tx_size),
            tx_size,
        })
    }
}

impl PartialEq for TransactionWithFee {
    fn eq(&self, other: &Self) -> bool {
        self.fee_per_byte == other.fee_per_byte
    }
}

impl PartialOrd for TransactionWithFee {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.fee_per_byte.cmp(&other.fee_per_byte))
    }
}

impl From<TransactionWithFee> for Transaction {
    fn from(other: TransactionWithFee) -> Self {
        other.tx.tx
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_atomic_swap() {}
}
