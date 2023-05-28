// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::ChainConfig;
use crate::consensus::*;
use crate::primitives::{BlockHeader, Hash256};
use crate::wallet::HDWallet;
use lazy_static::*;
use lru::LruCache;
use parking_lot::{
    Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard,
};
use std::collections::HashMap;
use std::io;
use std::num::NonZeroUsize;
use triomphe::Arc;

pub const LOGO: &[u8; 36124] = include_bytes!("./gui/img/logo_purple_square.png");

type GenesisCache = RwLock<HashMap<u8, Arc<RwLock<Option<Arc<BlockHeader>>>>>>;

lazy_static! {
    /// Genesis blocks cache
    static ref GENESIS_CACHE: GenesisCache = RwLock::new(HashMap::with_capacity(256));

    /// Wallet balances
    static ref WALLET_BLANCES: Mutex<HashMap<String, i128>> = Mutex::new(HashMap::new());

    /// Wallets
    pub static ref WALLETS: RwLock<HashMap<String, HDWallet>> = RwLock::new(HashMap::new());

    pub static ref LOGO_PIXELS: (Vec<u8>, u32, u32) = {
        let logo_with_format = image::io::Reader::with_format(
            io::Cursor::new(&crate::global::LOGO),
            image::ImageFormat::Png,
        );
        let pixels = logo_with_format.decode().unwrap().to_rgba8();
        (pixels.to_vec(), pixels.width(), pixels.height())
    };
}

/// Initialize globals
pub fn init() { }

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

#[cfg(test)]
mod tests {
    use super::*;
}
