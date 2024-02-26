// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::*;
use crate::primitives::{Hash256, TransactionWithFee};
use parking_lot::RwLock;
use std::collections::{BTreeSet, HashMap};
use std::marker::PhantomPinned;
use std::pin::Pin;
use std::ptr::NonNull;
use triomphe::Arc;

pub type PinnedMempool = Arc<RwLock<Pin<Box<Mempool>>>>;

#[derive(Debug)]
pub struct TransactionList(pub(crate) BTreeSet<NonNull<TransactionWithFee>>);
unsafe impl Send for TransactionList {}
unsafe impl Sync for TransactionList {}

#[derive(Debug)]
pub struct Mempool {
    pub(crate) tx_list: TransactionList,
    pub(crate) tx_map: HashMap<Hash256, TransactionWithFee>,
    pub(crate) current_size_bytes: u64,
    _pin: PhantomPinned,
}

impl Mempool {
    #[must_use]
    pub fn new() -> Pin<Box<Self>> {
        Box::pin(Self {
            tx_list: TransactionList(BTreeSet::new()),
            tx_map: HashMap::new(),
            current_size_bytes: 0,
            _pin: PhantomPinned,
        })
    }

    pub fn prune(&mut self) {}

    pub fn append(&mut self, tx: TransactionWithFee) -> Result<(), &'static str> {
        let tx_hash = *tx.hash().unwrap();

        // First check if we have the transaction present
        if self.tx_map.get(&tx_hash).is_some() {
            return Ok(());
        }

        // Write transaction and size
        self.current_size_bytes += u64::from(tx.tx_size);
        self.tx_map.insert(tx_hash, tx);
        let ptr = NonNull::from(self.tx_map.get(&tx_hash).unwrap());
        self.tx_list.0.insert(ptr);

        Ok(())
    }

    pub fn append_batch(&mut self, txs: Vec<TransactionWithFee>) -> Result<(), &'static str> {
        for tx in txs {
            self.append(tx)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::ChainConfig;
    use crate::primitives::*;
    use crate::vm::internal::VmTerm;
    use crate::vm::*;
    use rand::prelude::*;

    #[test]
    fn append_batch() {
        let txs: Vec<_> = (0..300).map(|_| get_random_tx()).collect();

        let mut mempool = Mempool::new();

        unsafe {
            let mut_ref: Pin<&mut _> = Pin::as_mut(&mut mempool);
            Pin::get_unchecked_mut(mut_ref)
                .append_batch(txs.clone())
                .unwrap();
        }

        for tx in &txs {
            assert_eq!(mempool.tx_map.get(tx.hash().unwrap()).unwrap(), tx as &_);
        }
    }

    fn get_random_tx() -> TransactionWithFee {
        let key = "test";
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
            VmTerm::Unsigned64(rand::thread_rng().gen()),
            VmTerm::Unsigned32(0),
        ];
        let mut input = Input {
            out: None,
            witness: None,
            spend_proof: None,
            colour_proof: None,
            colour_proof_without_address: None,
            spending_pkey: None,
            colour_script: None,
            colour_script_args: None,
            script: Script::new_coinbase(),
            input_flags: InputFlags::IsCoinbase,
            script_args,
            hash: None,
        };
        input.compute_hash(key);

        let mut tx = Transaction {
            chain_id,
            ins: vec![input],
            hash: None,
        };
        tx.compute_hash(key);
        let tx = TransactionWithSignatures {
            tx,
            signatures: vec![None],
        };
        TransactionWithFee::from_transaction(tx, 0, 0, [0; 32])
    }
}
