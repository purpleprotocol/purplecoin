//! This module wraps `blake2b_rfc` into a convenient hashing interface (`GeneralHasher`) and
//! exports the generalized `hash` function. Also exported is `hash_to_prime`, which works by
//! repeatedly `hash`ing a value together with an incrementing nonce until the output is prime.
use crate::uint::{u256, U256};
use lazy_static::*;
use lru::LruCache;
use parking_lot::Mutex;
use rand::Rng;
use rayon::prelude::*;
use rug::integer::Order;
use rug::Integer;
use std::hash::{Hash, Hasher};
use std::num::NonZeroUsize;
use xxhash_rust::xxh3::xxh3_128;

mod blake2b;
mod blake3_mod;
pub use blake2b::Blake2b;
pub use blake3_mod::Blake3;
pub mod primality;

// With this setup, we'll have around 100mb cache. TODO: Make this changeable
pub(crate) const INTERNAL_LRU_SHARDS: usize = 16;
pub(crate) const LRU_BYTES_PER_SHARD: usize = 7700000;

lazy_static! {
    pub(crate) static ref INTERNAL_LRU: Vec<Mutex<LruCache<[u8; 32], Integer>>> = {
        let mut v = Vec::with_capacity(INTERNAL_LRU_SHARDS);
        for _ in 0..INTERNAL_LRU_SHARDS {
            v.push(Mutex::new(LruCache::new(
                NonZeroUsize::new(LRU_BYTES_PER_SHARD / 64).unwrap(),
            )));
        }
        v
    };
}

#[inline]
fn hash_to_cache_key<T: Hash + ?Sized>(t: &T) -> ([u8; 32], usize) {
    let hash = hash(&(t, 0_u64));
    let mut bytes = [0; 8];
    bytes.copy_from_slice(&hash[..8]);
    let shard = jump_consistent_hash::hash(u64::from_le_bytes(bytes), INTERNAL_LRU_SHARDS) as usize;
    (hash, shard)
}

/// Bench utility
pub fn clear_cache_selectively<'a, T: Hash + 'a>(t: &'a [T])
// In order to make .par_iter() work
where
    [T]: IntoParallelRefIterator<'a>,
    <[T] as rayon::iter::IntoParallelRefIterator<'a>>::Iter: ParallelIterator,
    <<[T] as rayon::iter::IntoParallelRefIterator<'a>>::Iter as ParallelIterator>::Item: Hash + 'a,
{
    t.par_iter().for_each(|t| {
        let (cache_key, shard) = hash_to_cache_key(&t);
        let mut lru = (*INTERNAL_LRU)[shard].lock();
        lru.pop_entry(&cache_key);
    });
}

/// Bench utility
pub fn clear_cache() {
    for block in INTERNAL_LRU.iter() {
        block.lock().clear();
    }
}

/// Bench utility
pub fn clear_cache_percentage(percentage: f64) {
    for block in INTERNAL_LRU.iter() {
        let mut lock = block.lock();
        for _ in 0..lock.len() {
            if rand::thread_rng().gen_range(0.0..1.0) > percentage {
                lock.pop_lru();
            }
        }
    }
}

/// Like `std::hash::Hasher`, but general over output type.
pub trait GeneralHasher: Hasher {
    /// The associated output type of the Hasher.
    type Output;
    /// Similar to `Hasher::finish`, but consumes `self`.
    fn finalize(self) -> Self::Output;
}

// Note: We explicitly pass in the hasher constructor so we don't have to specify its type via
// generics. Rust has poor support for type applications, so if we wanted to pass `H` at the
// type-level, we'd need to fully specify `T` as well, which is a pain in the ass.
//
// Instead of writing:
// `hash::<Blake2b, (&G::Elem, &BigUint, &G::Elem)>(&(base, exp, result))`
//
// This lets us write:
// `hash(&Blake2b::default, &(base, exp, result))`

/// Hash using the general Hasher.
///
/// This function takes in the hash constructor as an argument for convenience.
#[inline]
pub fn hash<T: Hash + ?Sized>(t: &T) -> [u8; 32] {
    let mut h = Blake3::default();
    t.hash(&mut h);
    h.finalize()
}

/// Calls `hash` with a Blake3 hasher.
// pub fn blake2b<T: Hash + ?Sized>(t: &T) -> Integer {
//   Integer::from_digits(&hash(&Blake3::default, t), Order::Msf)
// }

/// Hashes `t` to an odd prime.
///
/// Uses `Blake3` as the hash function, and hashes with a counter until a prime is found via
/// probabilistic primality checking.
///
/// This function is optimized for 256-bit integers.
#[allow(clippy::module_name_repetitions)]
#[inline]
pub fn hash_to_prime<T: Hash + ?Sized>(t: &T) -> Integer {
    let mut counter = 0_u64;
    let mut counter2: u64 = 0_u64;
    let mut checked = [false; 256];
    let mut checked_count: usize = 1;
    let mut first_pass = true;
    let mut first_hash = [0; 32];
    let mut shard: usize = 0;
    loop {
        // First pass using blake3
        let mut hash = hash(&(t, counter));

        // Check the LRU cache
        if first_pass {
            let mut bytes = [0; 8];
            bytes.copy_from_slice(&hash[..8]);
            shard =
                jump_consistent_hash::hash(u64::from_le_bytes(bytes), INTERNAL_LRU_SHARDS) as usize;
            {
                let mut lru = (*INTERNAL_LRU)[shard].lock();

                if let Some(cached) = lru.get(&hash) {
                    return cached.clone();
                }
            }
            first_pass = false;
            first_hash = hash;
        }

        // Make the candidate prime odd. This gives ~7% performance gain on a 2018 Macbook Pro.
        hash[0] |= 1;
        let candidate_prime = u256(hash);
        if primality::is_prob_prime(&candidate_prime) {
            {
                let mut lru = (*INTERNAL_LRU)[shard].lock();
                lru.put(first_hash, Integer::from(candidate_prime));
            }
            return Integer::from(candidate_prime);
        }

        // Second pass
        //
        // Hash the result using xxh3_128 and then change the last byte
        // of the hash from the previous pass with every byte in the resulting
        // hash for 13 passes.
        //
        // This gives a ~14% performance gain on a 2019 Macbook Pro.
        checked[hash[31] as usize] = true;
        for _ in 0_u8..=13_u8 {
            let hashed_with_counter = xxh3_128(&[&hash[..], &counter2.to_le_bytes()].concat());
            let tail_bytes = hashed_with_counter.to_le_bytes();

            for i in 0..16 {
                if checked[tail_bytes[i] as usize] {
                    continue;
                }

                hash[31] = tail_bytes[i];
                checked[tail_bytes[i] as usize] = true;
                checked_count += 1;
                let candidate_prime = u256(hash);
                if primality::is_prob_prime(&candidate_prime) {
                    {
                        let mut lru = (*INTERNAL_LRU)[shard].lock();
                        lru.put(first_hash, Integer::from(candidate_prime));
                    }
                    return Integer::from(candidate_prime);
                }
            }

            counter2 += 1;

            if checked_count == 256 {
                break;
            }
        }
        checked = [false; 256];
        checked_count = 1;
        counter += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_blake2() {
        let data = b"martian cyborg gerbil attack";
        hash(data);
    }

    #[test]
    fn test_() {
        let b_1 = "boom i got ur boyfriend";
        let b_2 = "boom i got ur boyfriene";
        assert_ne!(b_1, b_2);
        let h_1 = hash_to_prime(b_1);
        let h_2 = hash_to_prime(b_2);
        assert_ne!(h_1, h_2);
        let mut digits1 = [0; 4];
        h_1.write_digits(&mut digits1, Order::Lsf);
        assert!(primality::is_prob_prime(&u256(digits1)));
        let mut digits2 = [0; 4];
        h_2.write_digits(&mut digits2, Order::Lsf);
        assert!(primality::is_prob_prime(&u256(digits2)));
    }
}
