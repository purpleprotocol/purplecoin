// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{Shard, ShardBackend};
use crate::consensus::Money;
use crate::primitives::{Hash256, Input, Output};
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
    pub fn get_outs(&self, height: u64, timestamp: i64, prev_block_hash: [u8; 32]) -> Vec<Output> {
        let key = format!("{}.shard.{}", SETTINGS.node.network_name, self.chain_id);
        let mut out_stack = vec![];
        let mut idx_map = HashMap::new();
        let mut ver_stack = VerificationStack::new();

        // Compute outputs
        for input in &self.ins {
            input.script.execute(
                &input.script_args,
                &self.ins,
                &mut out_stack,
                &mut idx_map,
                &mut ver_stack,
                [0; 32], // TODO: Inject seed here
                &key,
                SETTINGS.node.network_name.as_str(),
                VmFlags {
                    is_coinbase: input.is_coinbase(),
                    chain_height: height,
                    chain_timestamp: timestamp,
                    chain_id: self.chain_id,
                    validate_output_amounts: true,
                    build_stacktrace: false,
                    prev_block_hash,
                    in_binary: input.to_bytes_for_signing(),
                    spent_out: input.out.clone(),
                },
            );
        }

        out_stack
    }

    #[must_use]
    pub fn get_ins(&self) -> &[Input] {
        &self.ins
    }

    // /// Validate single transaction against the chain-state. Returns transaction fee if successful
    // pub fn verify_single<B: ShardBackend>(&self, shard: &Shard<B>) -> Result<Money, TxVerifyErr> {
    //     let key = shard.chain_config().get_chain_key(shard.chain_id());
    //     let ctx = signing_context(key.as_bytes());
    //     let mut transcripts: Vec<&[u8]> = Vec::with_capacity(self.ins.len());
    //     let mut public_keys: Vec<SchnorPK> = Vec::with_capacity(self.ins.len());
    //     let mut ins_sum: Money = 0;
    //     let mut outs_sum: Money = 0;
    //     let shard_height = shard.height().map_err(|_| TxVerifyErr::BackendErr)?;

    //     // Verify inputs
    //     for i in &self.ins {
    //         i.verify(
    //             key,
    //             shard_height,
    //             shard.chain_id,
    //             &mut ins_sum,
    //             &mut transcripts,
    //             &mut public_keys,
    //             shard,
    //         )?;
    //     }

    //     // Check that the sum of inputs is greater than that of the outputs
    //     if ins_sum < outs_sum {
    //         return Err(TxVerifyErr::InvalidAmount);
    //     }

    //     // TODO: Validate signatures another way for a single transaction
    //     // and validate aggregated signature in the block validation pipeline.
    //     //
    //     // // Verify all signatures against transcripts and public keys
    //     // if verify_batch(
    //     //     transcripts.iter().map(|m| ctx.bytes(m)),
    //     //     &public_keys,
    //     //     false,
    //     // )
    //     // .is_err()
    //     // {
    //     //     return Err(TxVerifyErr::InvalidSignature);
    //     // }

    //     Ok(ins_sum - outs_sum)
    // }

    /// Validate transaction against the chain-state and add to batch.
    /// To be used in the context of validating an entire block.
    ///
    /// Returns transaction fee if successful.
    pub fn verify_batch<'a, B: ShardBackend>(
        &'a self,
        transcripts: &mut Vec<&'a [u8]>,
        public_keys: &mut Vec<SchnorPK>,
        shard: &Shard<B>,
    ) -> Result<Money, TxVerifyErr> {
        unimplemented!();
        // let mut ins_sum: Money = 0;
        // let mut outs_sum: Money = 0;
        // let shard_height = shard.height().map_err(|_| TxVerifyErr::BackendErr)?;

        // // Verify inputs
        // for i in &self.ins {
        //     i.verify(shard_height, &mut ins_sum, transcripts, public_keys, shard)?;
        // }

        // // Check that the sum of inputs is greater than that of the outputs
        // if ins_sum < outs_sum {
        //     return Err(TxVerifyErr::InvalidAmount);
        // }

        // Ok(ins_sum - outs_sum)
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
    ColouredFeeNotAllowed,
    DuplicateCoinbase,
    DuplicateTxs,
    InvalidScriptHash,
    InvalidScriptExecution,
    InvalidCoinbase,
    BackendErr,
    Error(&'static str),
}

#[derive(Clone, Debug)]
/// Transaction with signatures used at the p2p layer for initial propagation.
pub struct TransactionWithSignatures {
    pub(crate) tx: Transaction,
    pub(crate) signatures: Vec<Option<SchnorSig>>,
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
        height: u64,
        timestamp: i64,
        prev_block_hash: [u8; 32],
    ) -> Self {
        let ins = other.tx.get_ins();
        let outs = other.tx.get_outs(height, timestamp, prev_block_hash);
        let ins_amount = ins
            .iter()
            .filter_map(|i| {
                // Filter coinbase and coloured outs
                let o = i.out.as_ref()?;
                i.out.as_ref().unwrap().address.as_ref()?;

                Some(o)
            })
            .fold(0, |acc, x| acc + x.amount);

        let outs_amount = outs
            .iter()
            .filter_map(|o| {
                // Filter coloured outs
                o.address.as_ref()?;

                Some(o)
            })
            .fold(0, |acc, x| acc + x.amount);

        let raw_fee = ins_amount - outs_amount;
        let tx_size = other.tx.to_bytes().len() as u32;

        Self {
            tx: other,
            raw_fee,
            fee_per_byte: raw_fee / i128::from(tx_size),
            tx_size,
        }
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
