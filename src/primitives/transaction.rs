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
        let mut to_add_temp = vec![];
        let mut to_delete_temp = vec![];

        // Verify inputs
        for (i, input) in self.ins.iter().enumerate() {
            let nonce = (i as u64).to_le_bytes();
            let input_seed_bytes: &[u8] = &[tx_seed_bytes, nonce.as_slice()].concat();
            let mut temp_ins_sum = 0;
            let mut temp_outs_sum = 0;
            // TODO: Only do this on failable inputs
            let to_add_bak = to_add_temp.clone();
            let to_delete_bak = to_delete_temp.clone();

            let result = input.verify(
                key,
                height,
                chain_id,
                &mut temp_ins_sum,
                &mut temp_outs_sum,
                &mut coloured_ins_sums,
                &mut coloured_outs_sums,
                timestamp,
                &block_reward,
                prev_block_hash,
                coinbase_allowed,
                &mut to_add_temp,
                &mut to_delete_temp,
                ver_stack,
                idx_map,
                input_seed_bytes,
                self.ins.as_slice(),
                validate_coloured_coinbase,
            );

            match (result, input.is_failable()) {
                (Err(err), false) => return Err(err), // Not failable so the whole transaction is invalid
                (Err(_), true) => break, // Stop the rest of the transaction execution at this point
                (Ok(()), true) => {
                    // Check that the sum of inputs is greater than that of the outputs
                    if temp_ins_sum < temp_outs_sum {
                        // Revert state. TODO: Optimise this. Simply pop the extra state.
                        to_add_temp = to_add_bak;
                        to_delete_temp = to_delete_bak;
                        break;
                    }

                    if input.is_coloured() {
                        let mut b = false;
                        // Verify coloured sums
                        for (k, ins_sum) in &coloured_ins_sums {
                            let outs_sum = coloured_outs_sums.get(k).unwrap_or(&0);
                            if ins_sum < outs_sum {
                                b = true;
                                break;
                            }
                        }
                        if b {
                            // Revert state. TODO: Optimise this. Simply pop the extra state.
                            to_add_temp = to_add_bak;
                            to_delete_temp = to_delete_bak;
                            break;
                        }
                    }

                    // Execution succeeded, flush changes.
                    ins_sum += temp_ins_sum;
                    outs_sum += temp_outs_sum;
                }
                _ => {
                    // Execution succeeded, flush changes.
                    ins_sum += temp_ins_sum;
                    outs_sum += temp_outs_sum;
                }
            }
        }

        // Check that the sum of inputs is greater than that of the outputs
        if ins_sum < outs_sum {
            return Err(TxVerifyErr::InvalidAmount);
        }

        // Verify coloured sums
        for (k, ins_sum) in &coloured_ins_sums {
            let outs_sum = coloured_outs_sums.get(k).unwrap_or(&0);
            if ins_sum < outs_sum {
                return Err(TxVerifyErr::InvalidAmount);
            }
        }

        // Execution succeeded, flush changes.
        to_add.extend(to_add_temp);
        to_delete.extend(to_delete_temp);

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
                public_keys.push(pub_key.0);
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
    use crate::primitives::{compute_colour_hash, ColouredAddress, InputFlags, Keypair};
    use crate::vm::internal::VmTerm;
    use crate::vm::Script;

    fn xpu_ss_input_to_address_of_amount(amount: Money, to: Address, key: &str) -> Input {
        let keypair = Keypair::new();
        let address = keypair.to_address();
        let script = Script::new_simple_spend();
        let script_hash = script.to_script_hash(key);
        let mut out = Output {
            amount: amount + 10, // Add some psats for a tx fee
            script_hash: script_hash.clone(),
            address: Some(address),
            inputs_hash: Hash160::random(),
            idx: 0,
            coloured_address: None,
            coinbase_height: None,
            script_outs: vec![],
            hash: None,
        };

        out.compute_hash(key);

        let mut input = Input {
            out: Some(out),
            script,
            input_flags: InputFlags::Plain,
            spending_pkey: Some(keypair.public()),
            script_args: vec![
                VmTerm::Signed128(amount),
                VmTerm::Hash160(to.0),
                VmTerm::Hash160(script_hash.0),
            ],
            witness: Some(accumulator::Witness::empty()),
            ..Default::default()
        };
        input.compute_hash(key);
        input
    }

    fn xpu_ss_failable_input_to_address_of_amount(amount: Money, to: Address, key: &str) -> Input {
        let keypair = Keypair::new();
        let address = keypair.to_address();
        let script = Script::new_simple_spend();
        let script_hash = script.to_script_hash(key);
        let mut out = Output {
            amount: amount + 10, // Add some psats for a tx fee
            script_hash: script_hash.clone(),
            address: Some(address),
            inputs_hash: Hash160::random(),
            idx: 0,
            coloured_address: None,
            coinbase_height: None,
            script_outs: vec![],
            hash: None,
        };

        out.compute_hash(key);

        let mut input = Input {
            out: Some(out),
            script,
            input_flags: InputFlags::FailablePlain,
            spending_pkey: Some(keypair.public()),
            script_args: vec![
                VmTerm::Signed128(amount),
                VmTerm::Hash160(to.0),
                VmTerm::Hash160(script_hash.0),
            ],
            witness: Some(accumulator::Witness::empty()),
            ..Default::default()
        };
        input.compute_hash(key);
        input
    }

    fn ss_input_to_address_of_asset_and_amount(
        amount: Money,
        to: ColouredAddress,
        key: &str,
    ) -> Input {
        let keypair = Keypair::new();
        let colour_script = Script::new_nop_script();
        let (colour_hash, colour_kernel) =
            compute_colour_hash(&colour_script, &[], &keypair.public());
        let address = keypair.to_coloured_address(&colour_hash);
        let script = Script::new_simple_spend();
        let script_hash = script.to_script_hash(key);
        let mut out = Output {
            amount,
            script_hash: script_hash.clone(),
            coloured_address: Some(address),
            inputs_hash: Hash160::random(),
            idx: 0,
            address: None,
            coinbase_height: None,
            script_outs: vec![],
            hash: None,
        };

        out.compute_hash(key);

        let mut input = Input {
            out: Some(out),
            script,
            colour_script: Some(colour_script),
            colour_script_args: Some(vec![]),
            input_flags: InputFlags::IsColoured,
            spending_pkey: Some(keypair.public()),
            colour_kernel: Some(colour_kernel),
            script_args: vec![
                VmTerm::Signed128(amount),
                VmTerm::Hash160(to.address),
                VmTerm::Hash160(script_hash.0),
            ],
            witness: Some(accumulator::Witness::empty()),
            ..Default::default()
        };
        input.compute_hash(key);
        input
    }

    struct ExecResult {
        pub to_add: Vec<Output>,
        pub to_delete: Vec<(
            Output,
            accumulator::Witness<accumulator::group::Rsa2048, Output>,
        )>,
        pub idx_map: HashMap<Hash160, u16>,
        pub ver_stack: VerificationStack,
    }

    /// Helper to execute a simple transaction
    fn exec_tx(tx: &Transaction, key: &str, cb: impl Fn(Result<Money, TxVerifyErr>, ExecResult)) {
        let mut to_add = vec![];
        let mut to_delete = vec![];
        let mut idx_map = HashMap::new();
        let mut ver_stack = VerificationStack::new();

        let result = tx.verify_single(
            key,
            0,
            0,
            0,
            Hash256::zero(),
            0,
            false,
            &mut to_add,
            &mut to_delete,
            &mut ver_stack,
            &mut idx_map,
            &[0; 32],
            |_| Ok(()),
        );

        cb(
            result,
            ExecResult {
                to_add,
                to_delete,
                idx_map,
                ver_stack,
            },
        );
    }

    macro_rules! tx {
        ($($x:expr),+ $(,)?) => (
            Transaction {
                chain_id: 0,
                ins: vec![$($x),+],
                hash: None,
            }
        );
    }

    #[test]
    fn test_simple_spend() {
        let address = Address::random();
        let key = "test_key";
        let amount = 10_000_000;
        let tx = tx![xpu_ss_input_to_address_of_amount(
            amount,
            address.clone(),
            key,
        )];

        exec_tx(&tx, key, |res, data| {
            let script = Script::new_simple_spend();
            let script_hash = script.to_script_hash(key);

            assert_eq!(res.unwrap(), 10); // Check tx fee
            assert_eq!(data.to_add.len(), 1);
            assert_eq!(data.to_delete.len(), 1);
            assert_eq!(data.to_add[0].amount, amount); // Check out amount
            assert_eq!(data.to_add[0].address.as_ref().unwrap(), &address); // Check receiver address
            assert_eq!(data.to_add[0].script_hash, script_hash); // Check script hash
        });
    }

    #[test]
    fn two_simple_spends() {
        let address = Address::random();
        let key = "test_key";
        let amount = 10_000_000;
        let tx = tx![
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key)
        ];

        exec_tx(&tx, key, |res, data| {
            let script = Script::new_simple_spend();
            let script_hash = script.to_script_hash(key);

            assert_eq!(res.unwrap(), 20); // Check tx fee
            assert_eq!(data.to_add.len(), 1);
            assert_eq!(data.to_delete.len(), 2);
            assert_eq!(data.to_add[0].amount, amount * 2); // Check out amount
            assert_eq!(data.to_add[0].address.as_ref().unwrap(), &address); // Check receiver address
            assert_eq!(data.to_add[0].script_hash, script_hash); // Check script hash
        });
    }

    #[test]
    fn fails_on_sum_of_inputs_lower_than_of_outputs() {
        let address = Address::random();
        let key = "test_key";
        let amount = 10_000_000;
        let mut input = xpu_ss_input_to_address_of_amount(amount, address.clone(), key);
        input.script_args[0] = VmTerm::Signed128(10_000_000_000);
        let tx = tx![input];

        exec_tx(&tx, key, |res, data| {
            assert_eq!(res, Err(TxVerifyErr::InvalidAmount));
            assert_eq!(data.to_add.len(), 0);
            assert_eq!(data.to_delete.len(), 0);
        });
    }

    #[test]
    fn fails_on_sum_of_inputs_lower_than_of_outputs_2() {
        let address = Address::random();
        let key = "test_key";
        let amount = 10_000_000;
        let mut input = xpu_ss_input_to_address_of_amount(amount, address.clone(), key);
        input.script_args[0] = VmTerm::Signed128(10_000_000_000);
        let tx = tx![
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            input,
        ];

        exec_tx(&tx, key, |res, data| {
            assert_eq!(res, Err(TxVerifyErr::InvalidAmount));
            assert_eq!(data.to_add.len(), 0);
            assert_eq!(data.to_delete.len(), 0);
        });
    }

    #[test]
    fn partially_fails_on_sum_of_inputs_lower_than_of_outputs() {
        let address = Address::random();
        let key = "test_key";
        let amount = 10_000_000;
        let mut input = xpu_ss_failable_input_to_address_of_amount(amount, address.clone(), key);
        input.script_args[0] = VmTerm::Signed128(10_000_000_000);
        let tx = tx![
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            input,
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
            xpu_ss_input_to_address_of_amount(amount, address.clone(), key),
        ];

        exec_tx(&tx, key, |res, data| {
            assert!(res.is_ok());
            assert_eq!(data.to_add.len(), 1);
            assert_eq!(data.to_delete.len(), 3);
        });
    }

    // #[test]
    // fn test_simple_atomic_swap() {
    //     let key = "test_key";
    //     let amount = 10_000_000;
    //     let tx = Transaction {
    //         chain_id: 0,
    //         ins: vec![ss_input_to_address_of_asset_and_amount(
    //             amount, &address, key,
    //         )],
    //         hash: None,
    //     };
    // }
}
