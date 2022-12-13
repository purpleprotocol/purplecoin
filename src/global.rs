// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::ChainConfig;
use crate::consensus::*;
use crate::primitives::{BlockHeader, Hash256};
use lazy_static::*;
use lru::LruCache;
use parking_lot::{
    Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard,
};
use rust_randomx::Context;
use std::collections::HashMap;
use std::num::NonZeroUsize;
use triomphe::Arc;

type RandomXCtxStore = Mutex<LruCache<Hash256, Arc<Mutex<Option<Arc<Context>>>>>>;
type GenesisCache = RwLock<HashMap<u8, Arc<RwLock<Option<Arc<BlockHeader>>>>>>;

lazy_static! {
    /// RandomX
    ///
    /// * 256mb x 4 = 1024mb max memory in slow mode by default
    /// * 2080mb x 4 = 8320mb max memory in fast mode by default
    static ref RANDOMX_CTX_SIZE_MUX: Mutex<usize> = Mutex::new(4);
    static ref RANDOMX_CTX_STORE: RandomXCtxStore = Mutex::new(LruCache::new(NonZeroUsize::new(*RANDOMX_CTX_SIZE_MUX.lock()).unwrap()));
    static ref RANDOMX_FAST_MODE_MUX: Mutex<bool> = Mutex::new(false);
    static ref RANDOMX_FAST_MODE: bool = *RANDOMX_FAST_MODE_MUX.lock();

    /// Genesis blocks cache
    static ref GENESIS_CACHE: GenesisCache = RwLock::new(HashMap::with_capacity(256));

    /// Wallet balances
    static ref WALLET_BLANCES: Mutex<HashMap<String, i128>> = Mutex::new(HashMap::new());
}

/// Initialize globals
pub fn init(ctx_size: usize, randomx_fast: bool) {
    {
        let mut rxctxsmux = RANDOMX_CTX_SIZE_MUX.lock();
        *rxctxsmux = ctx_size;
    }

    {
        let mut rxfmmux = RANDOMX_FAST_MODE_MUX.lock();
        *rxfmmux = randomx_fast;
    }
}

pub fn set_balance(wallet: &str, balance: i128) {
    WALLET_BLANCES.lock().insert(wallet.to_owned(), balance);
}

pub fn increment_balance(wallet: &str, incr: i128) -> Option<i128> {
    debug_assert!(incr > 0);
    let mut lock = WALLET_BLANCES.lock();
    let mut balance = lock.get_mut(wallet)?;
    *balance += incr;
    Some(*balance)
}

pub fn get_balance(wallet: &str) -> i128 {
    *WALLET_BLANCES.lock().get(wallet).unwrap_or(&0)
}

pub fn get_cached_genesis(chain_id: u8, chain_config: &ChainConfig) -> Arc<BlockHeader> {
    let mut gcmux = GENESIS_CACHE.upgradable_read();

    match gcmux.get(&chain_id).cloned() {
        Some(genmux) => {
            RwLockUpgradableReadGuard::unlock_fair(gcmux);
            let mut genmux = genmux.upgradable_read();
            match genmux.as_ref().cloned() {
                Some(v) => v,
                None => {
                    let mut genmux = RwLockUpgradableReadGuard::upgrade(genmux);
                    let genesis = Arc::new(BlockHeader::genesis(chain_id, chain_config));
                    *genmux = Some(genesis.clone());
                    genesis
                }
            }
        }
        None => {
            let mut gcmux = RwLockUpgradableReadGuard::upgrade(gcmux);
            let genmux = gcmux.get(&chain_id).cloned();
            if let Some(genmux) = genmux {
                RwLockWriteGuard::unlock_fair(gcmux);
                genmux.read().as_ref().cloned().unwrap()
            } else {
                let genmux = Arc::new(RwLock::new(None));
                gcmux.insert(chain_id, genmux.clone());
                let mut genmux = genmux.write();
                RwLockWriteGuard::unlock_fair(gcmux);
                let genesis = Arc::new(BlockHeader::genesis(chain_id, chain_config));
                *genmux = Some(genesis.clone());
                genesis
            }
        }
    }
}

/// Retrieves the RandomX context for the given key
pub fn get_randomx_ctx(key: &str) -> Arc<Context> {
    let nn: &str = &crate::settings::SETTINGS.node.network_name;
    let key = format!("{}.{}.{}", RANDOMX_KEY_PREFIX, nn, key);
    let key = Hash256::hash_from_slice(key, "purplecoinminer");
    let mut nnmux = (*RANDOMX_CTX_STORE).lock();

    match nnmux.get(&key).cloned() {
        Some(ctx) => {
            MutexGuard::unlock_fair(nnmux);
            ctx.lock().as_ref().unwrap().clone()
        }
        None => {
            let ctxmux = Arc::new(Mutex::new(None));
            nnmux.put(key, ctxmux.clone());
            let mut ctxmux = ctxmux.lock();
            MutexGuard::unlock_fair(nnmux);
            let ctx = Arc::new(Context::new(key.as_bytes(), *RANDOMX_FAST_MODE));
            *ctxmux = Some(ctx.clone());
            ctx
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
