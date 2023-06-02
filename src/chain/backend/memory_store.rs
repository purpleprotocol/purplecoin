// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use parking_lot::RwLock;
use std::cmp::Eq;
use std::collections::HashMap;
use std::hash::Hash;
use triomphe::Arc;
use xxhash_rust::xxh3::xxh3_64;

type Store<K, V> = RwLock<HashMap<K, V>>;

#[derive(Debug, Clone)]
pub struct MemoryStore<K: AsRef<[u8]> + Hash + PartialEq + Eq, V: Clone> {
    shards: Arc<Vec<Store<K, V>>>,
}

impl<K: AsRef<[u8]> + Hash + PartialEq + Eq, V: Clone> MemoryStore<K, V> {
    pub fn new() -> Self {
        let mut shards = Vec::new();

        for _ in 0..num_cpus::get() {
            shards.push(RwLock::new(HashMap::new()));
        }

        Self {
            shards: Arc::new(shards),
        }
    }

    pub fn get(&self, k: &K) -> Option<V> {
        let hashed_key = xxh3_64(k.as_ref());
        let shard = jump_consistent_hash::hash(hashed_key, num_cpus::get()) as usize;
        let guard = self.shards[shard].read();

        guard.get(k).cloned()
    }

    pub fn put(&self, k: K, v: V) -> Option<V> {
        let hashed_key = xxh3_64(k.as_ref());
        let shard = jump_consistent_hash::hash(hashed_key, num_cpus::get()) as usize;
        let mut guard = self.shards[shard].write();

        guard.insert(k, v)
    }

    pub fn delete(&self, k: &K) -> Option<V> {
        let hashed_key = xxh3_64(k.as_ref());
        let shard = jump_consistent_hash::hash(hashed_key, num_cpus::get()) as usize;
        let mut guard = self.shards[shard].write();

        guard.remove(k)
    }
}
