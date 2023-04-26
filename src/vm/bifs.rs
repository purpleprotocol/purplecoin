// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::primitives::{Hash256, Hash512};
use crate::vm::internal::VmTerm as Term;

use blake2::digest::{Update, VariableOutput};
use blake2::{Blake2bVar, Blake2s, Blake2sVar, Digest as Blake2Digest};
use ripemd::{Digest as RipemdDigest, Ripemd160};
use sha2::{Digest as ShaDigest, Sha256, Sha512};
use sha3::{Digest as KeccakDigest, Keccak256, Keccak512};

pub fn ripemd160(term: &Term) -> Term {
    let mut hasher = Ripemd160::new();
    RipemdDigest::update(&mut hasher, term.to_bytes_raw());
    let hashed_term = hasher.finalize();

    Term::Hash160(hashed_term.into())
}

pub fn sha256(term: &Term) -> Term {
    let mut hasher = Sha256::new();
    ShaDigest::update(&mut hasher, term.to_bytes_raw());
    let hashed_term = hasher.finalize();

    Term::Hash256(hashed_term.into())
}

pub fn sha512(term: &Term) -> Term {
    let mut hasher = Sha512::new();
    ShaDigest::update(&mut hasher, term.to_bytes_raw());
    let hashed_term = hasher.finalize();

    Term::Hash512(hashed_term.into())
}

pub fn keccak256(term: &Term) -> Term {
    let mut hasher = Keccak256::new();
    KeccakDigest::update(&mut hasher, term.to_bytes_raw());
    let hashed_term = hasher.finalize();

    Term::Hash256(hashed_term.into())
}

pub fn keccak512(term: &Term) -> Term {
    let mut hasher = Keccak512::new();
    KeccakDigest::update(&mut hasher, term.to_bytes_raw());
    let hashed_term = hasher.finalize();

    Term::Hash512(hashed_term.into())
}

pub fn blake2b_256(term: &Term) -> Term {
    let mut hasher = Blake2bVar::new(32).unwrap();
    hasher.update(&term.to_bytes_raw());
    let hashed_term = hasher.finalize_boxed();

    Term::Hash256(hashed_term.to_vec().try_into().unwrap())
}

pub fn blake2b_512(term: &Term) -> Term {
    let mut hasher = Blake2bVar::new(64).unwrap();
    hasher.update(&term.to_bytes_raw());
    let hashed_term = hasher.finalize_boxed();

    Term::Hash512(hashed_term.to_vec().try_into().unwrap())
}

pub fn blake2s_256(term: &Term) -> Term {
    let mut hasher = Blake2sVar::new(32).unwrap();
    hasher.update(&term.to_bytes_raw());
    let hashed_term = hasher.finalize_boxed();

    Term::Hash256(hashed_term.to_vec().try_into().unwrap())
}

pub fn blake2s_512(term: &Term) -> Term {
    let mut hasher = Blake2sVar::new(64).unwrap();
    hasher.update(&term.to_bytes_raw());
    let hashed_term = hasher.finalize_boxed();

    Term::Hash512(hashed_term.to_vec().try_into().unwrap())
}

pub fn blake3_256(term: &Term) -> Term {
    let mut out_buffer = [0u8; 32];
    let mut hasher = blake3::Hasher::new();
    hasher.update(&term.to_bytes_raw());
    let mut out = hasher.finalize_xof();
    out.fill(&mut out_buffer);

    Term::Hash256(out_buffer)
}

pub fn blake3_512(term: &Term) -> Term {
    let mut out_buffer = [0u8; 64];
    let mut hasher = blake3::Hasher::new();
    hasher.update(&term.to_bytes_raw());
    let mut out = hasher.finalize_xof();
    out.fill(&mut out_buffer);

    Term::Hash512(out_buffer)
}

pub fn blake3_256_internal(term: &Term, key: &str) -> Term {
    let primitive_hash = Hash256::hash_from_slice(&term.to_bytes_raw(), key);

    Term::Hash256(primitive_hash.0)
}

pub fn blake3_512_internal(term: &Term, key: &str) -> Term {
    let primitive_hash = Hash512::hash_from_slice(&term.to_bytes_raw(), key);

    Term::Hash512(primitive_hash.0)
}
