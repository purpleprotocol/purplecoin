// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use std::sync::Arc;
use std::collections::HashMap;
use parking_lot::RwLock;

type Store<K, V> = RwLock<HashMap<K, V>>;

#[derive(Debug, Clone)]
pub struct MemoryStore<K, V: Clone> {
    shards: Arc<Vec<Store<K, V>>>,
}

impl<K, V: Clone> MemoryStore<K, V> {
    pub fn new() -> Self {
        let mut shards = Vec::new();

        for _ in 0..num_cpus::get() {
            shards.push(RwLock::new(HashMap::new()));
        }

        Self {
            shards: Arc::new(shards),
        }
    }

    pub fn get(k: &K) -> Option<V> {
        unimplemented!();
    }

    pub fn put(k: K, v: V) -> Option<V> {
        unimplemented!();
    }

    pub fn delete(k: K) -> Option<V> {
        unimplemented!();
    }
}