//! This module wraps `blake2b_rfc` into a convenient hashing interface (`GeneralHasher`) and
//! exports the generalized `hash` function. Also exported is `hash_to_prime`, which works by
//! repeatedly `hash`ing a value together with an incrementing nonce until the output is prime.
use crate::uint::{u256, U256};
use lazy_static::*;
use lru::LruCache;
use parking_lot::Mutex;
use rand::Rng;
use rayon::prelude::*;

use fx_hash::FxHasher64;
use rug::Integer;
use std::hash::{Hash, Hasher};
use std::num::NonZeroUsize;

mod blake2b;
mod blake3_mod;
mod fx_hash;
pub use blake2b::Blake2b;
pub use blake3_mod::Blake3;
pub mod primality;

// With this setup, we'll have around 100mb cache. TODO: Make this changeable
pub(crate) const CACHE_BYTES_TOTAL: usize = 100_000_000;

lazy_static! {
    pub(crate) static ref INTERNAL_LRU_SHARDS: usize = num_cpus::get();
    pub(crate) static ref INTERNAL_LRU: Vec<Mutex<LruCache<[u8; 32], Integer>>> = {
        let bytes_per_shard = CACHE_BYTES_TOTAL / *INTERNAL_LRU_SHARDS;
        let mut v = Vec::with_capacity(*INTERNAL_LRU_SHARDS);
        for _ in 0..*INTERNAL_LRU_SHARDS {
            v.push(Mutex::new(LruCache::new(
                NonZeroUsize::new(bytes_per_shard / 64).unwrap(),
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
    let shard =
        jump_consistent_hash::hash(u64::from_le_bytes(bytes), *INTERNAL_LRU_SHARDS) as usize;
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

// /// Calls `hash` with a Blake3 hasher.
// pub fn blake2b<T: Hash + ?Sized>(t: &T) -> Integer {
//     Integer::from_digits(&hash(t), Order::Msf)
// }

/// Hashes `t` to an odd prime.
///
/// Uses `Blake3` as the hash function, and hashes with a counter until a prime is found via
/// probabilistic primality checking.
///
/// This function is optimized for 256-bit integer
#[allow(clippy::module_name_repetitions)]
#[inline]
pub fn hash_to_prime<T: Hash + ?Sized>(t: &T) -> Integer {
    hash_to_prime_with_counter(t, None).0
}

#[allow(clippy::module_name_repetitions)]
#[inline]
pub fn hash_to_prime_with_counter<T: Hash + ?Sized>(t: &T, counters: Option<u8>) -> (Integer, u8) {
    let mut counter = 0;
    let mut hash = hash(&t);
    hash[0] |= 1;
    let mut candidate_prime = u256(hash);
    let two = u256(2);
    loop {
        if primality::is_prob_prime(&candidate_prime) {
            let prime = Integer::from(candidate_prime);
            return (prime, counter);
        }
        counter += 1;
        candidate_prime += two;
    }
}

#[allow(clippy::module_name_repetitions)]
#[inline]
pub fn hash_to_prime_check_counter<T: Hash + ?Sized>(t: &T, counter: u8) -> Option<Integer> {
    let mut hash = hash(&t);
    hash[0] |= 1;
    let counter: U256 = (counter as u64 * 2).into();
    let candidate_prime = u256(hash);
    let candidate_prime: U256 = candidate_prime + counter;
    if primality::is_prob_prime(&candidate_prime) {
        let prime = Integer::from(candidate_prime);
        Some(prime)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::integer::Order;

    #[test]
    fn deterministic() {
        let t = "tesgggt_datgga5344tretrfdserewfdsfdsrewtrexbkhjb";
        let h1 = hash_to_prime_with_counter(t, None);
        let h2 = hash_to_prime_with_counter(t, None);
        assert_eq!(h1.0, h2.0);
    }

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
