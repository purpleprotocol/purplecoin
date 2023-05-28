// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use bech32::{self, FromBase32, ToBase32, Variant};
use bincode::{Decode, Encode};
use bloomfilter::Bloom;
use lazy_static::*;
use merkletree::hash::{Algorithm, Hashable};
use merkletree::merkle::Element;
use rand::Rng;
use schnorrkel::PreparedBatch;
use schnorrkel::PublicKey as SchnorrPubKey;
use schnorrkel::Signature as SchnorrSignature;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::convert::From;
use std::fmt;
use std::hash::Hash as HashTrait;
use std::hash::Hasher;
use std::str;
use zeroize::Zeroize;

pub const ADDRESS_BYTES: usize = 20;
pub const COLOURED_ADDRESS_BYTES: usize = 40;

const HASH_KEY_PREFIX: &str = "purplecoin.hash.";

lazy_static! {
    static ref HASH_KEY160_OWNED: String = format!("{}", 20);
    static ref HASH_KEY160: &'static str = &HASH_KEY160_OWNED;
    static ref HASH_KEY256_OWNED: String = format!("{}", 32);
    static ref HASH_KEY256: &'static str = &HASH_KEY256_OWNED;
    static ref HASH_KEY512_OWNED: String = format!("{}", 64);
    static ref HASH_KEY512: &'static str = &HASH_KEY512_OWNED;
}

#[derive(Clone, PartialEq, Eq, HashTrait, Encode, Decode)]
pub struct ColouredAddress(pub [u8; COLOURED_ADDRESS_BYTES]);

impl ColouredAddress {
    pub fn zero() -> Self {
        Self([0; COLOURED_ADDRESS_BYTES])
    }

    pub fn to_bech32(&self, hrp: &str) -> String {
        bech32::encode(hrp, self.0.to_base32(), Variant::Bech32m).unwrap()
    }

    pub fn from_bech32(encoded: &str) -> Result<Self, &'static str> {
        let (_hrp, data, _variant) = bech32::decode(encoded).map_err(|_| "invalid address")?;
        let data: Vec<u8> = Vec::<u8>::from_base32(&data).map_err(|_| "invalid address")?;
        let mut out = Self([0; COLOURED_ADDRESS_BYTES]);
        out.0.copy_from_slice(&data);
        Ok(out)
    }

    /// Validate against public key
    pub fn validate(&self, public_key: &PublicKey, colour_hash: &Hash160) -> bool {
        self == &public_key.to_coloured_address(colour_hash)
    }
}

impl Serialize for ColouredAddress {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        String::serialize(&self.to_bech32("pu"), serializer)
    }
}

impl<'de> Deserialize<'de> for ColouredAddress {
    fn deserialize<D>(deserializer: D) -> Result<ColouredAddress, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string = String::deserialize(deserializer)?;
        ColouredAddress::from_bech32(&string)
            .map_err(|err| serde::de::Error::custom(err.to_owned()))
    }
}

impl fmt::Debug for ColouredAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ColouredAddress")
            .field(&self.to_bech32("pu"))
            .finish()
    }
}

#[derive(Clone, PartialEq, Eq, HashTrait, Encode, Decode)]
pub struct Address(pub [u8; ADDRESS_BYTES]);

impl Address {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn zero() -> Self {
        Self([0; ADDRESS_BYTES])
    }

    pub fn to_bech32(&self, hrp: &str) -> String {
        bech32::encode(hrp, self.0.to_base32(), Variant::Bech32m).unwrap()
    }

    pub fn from_bech32(encoded: &str) -> Result<Self, &'static str> {
        let (_hrp, data, _variant) = bech32::decode(encoded).map_err(|_| "invalid address")?;
        let data: Vec<u8> = Vec::<u8>::from_base32(&data).map_err(|_| "invalid address")?;
        let mut out = Self([0; ADDRESS_BYTES]);
        out.0.copy_from_slice(&data);
        Ok(out)
    }

    /// Validate against public key
    pub fn validate(&self, public_key: &PublicKey) -> bool {
        self == &public_key.to_address()
    }

    #[cfg(test)]
    pub fn random() -> Self {
        Self(rand::thread_rng().gen())
    }
}

impl Serialize for Address {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        String::serialize(&self.to_bech32("pu"), serializer)
    }
}

impl<'de> Deserialize<'de> for Address {
    fn deserialize<D>(deserializer: D) -> Result<Address, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string = String::deserialize(deserializer)?;
        Address::from_bech32(&string).map_err(|err| serde::de::Error::custom(err.to_owned()))
    }
}

impl fmt::Debug for Address {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Address")
            .field(&self.to_bech32("pu"))
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PublicKey(pub SchnorrPubKey);

impl Zeroize for PublicKey {
    fn zeroize(&mut self) {}
}

impl PublicKey {
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        if bytes.len() != 32 {
            return Err("invalid slice length! expected 32");
        }

        Ok(Self(
            SchnorrPubKey::from_bytes(bytes).map_err(|_| "could not decode public key")?,
        ))
    }

    pub fn zero() -> Self {
        let bytes = vec![0; 32];
        Self::from_bytes(&bytes).unwrap()
    }

    #[inline]
    pub fn to_address(&self) -> Address {
        let mut address = Address([0; ADDRESS_BYTES]);
        let mut hash1 = [0; 32];
        let pub_bytes = self.0.to_bytes();
        let mut hasher = blake3::Hasher::new_derive_key(&HASH_KEY256);
        hasher.update(&pub_bytes);
        let mut out = hasher.finalize_xof();
        out.fill(&mut hash1);
        let mut hasher = blake3::Hasher::new_derive_key(&HASH_KEY160);
        hasher.update(&hash1);
        let mut out = hasher.finalize_xof();
        out.fill(&mut address.0);
        address
    }

    #[inline]
    pub fn to_coloured_address(&self, colour_hash: &Hash160) -> ColouredAddress {
        let mut out_bytes = [0; COLOURED_ADDRESS_BYTES];
        let mut hash1 = [0; 32];
        let pub_bytes = self.0.to_bytes();
        let mut hasher = blake3::Hasher::new_derive_key(&HASH_KEY256);
        hasher.update(&pub_bytes);
        let mut out = hasher.finalize_xof();
        out.fill(&mut hash1);
        let mut hasher = blake3::Hasher::new_derive_key(&HASH_KEY160);
        hasher.update(&hash1);
        let mut out = hasher.finalize_xof();
        let mut hash_bytes = [0; 20];
        out.fill(&mut hash_bytes);
        out_bytes.copy_from_slice(&[hash_bytes.as_slice(), colour_hash.as_bytes()].concat());

        ColouredAddress(out_bytes)
    }
}

impl Encode for PublicKey {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.0.to_bytes(), encoder)?;
        Ok(())
    }
}

impl Decode for PublicKey {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let pk_bytes: [u8; schnorrkel::PUBLIC_KEY_LENGTH] = bincode::Decode::decode(decoder)?;
        let result = SchnorrPubKey::from_bytes(&pk_bytes).map_err(|_| {
            bincode::error::DecodeError::OtherString("invalid public key format".to_owned())
        })?;
        Ok(Self(result))
    }
}

#[derive(Clone, PartialEq)]
pub struct Signature(pub SchnorrSignature);

impl Encode for Signature {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.0.to_bytes(), encoder)?;
        Ok(())
    }
}

impl Decode for Signature {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let pk_bytes: [u8; schnorrkel::SIGNATURE_LENGTH] = bincode::Decode::decode(decoder)?;
        let result = SchnorrSignature::from_bytes(&pk_bytes).map_err(|_| {
            bincode::error::DecodeError::OtherString("invalid signature format".to_owned())
        })?;
        Ok(Self(result))
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature")
            .field(&hex::encode(self.0.to_bytes()))
            .finish()
    }
}

#[derive(PartialEq, Eq, Encode, Decode, Clone, HashTrait, Zeroize, Serialize, Deserialize)]
pub struct Hash160(pub [u8; 20]);

impl Hash160 {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn zero() -> Self {
        Self([0; 20])
    }

    pub fn to_address(&self) -> Address {
        Address(self.0)
    }

    #[inline]
    pub fn hash_from_slice<T: AsRef<[u8]>>(slice: T, key: &str) -> Self {
        let mut out_hash = Hash160([0; 20]);
        let mut hash1 = [0; 32];
        let key1 = &[
            HASH_KEY_PREFIX.as_bytes(),
            HASH_KEY256.as_bytes(),
            ".".as_bytes(),
            key.as_bytes(),
        ]
        .concat();
        let key1 = unsafe { str::from_utf8_unchecked(key1) };
        let mut hasher = blake3::Hasher::new_derive_key(key1);
        hasher.update(slice.as_ref());
        let mut out = hasher.finalize_xof();
        out.fill(&mut hash1);
        let key = &[
            HASH_KEY_PREFIX.as_bytes(),
            HASH_KEY160.as_bytes(),
            ".".as_bytes(),
            key.as_bytes(),
        ]
        .concat();
        let key = unsafe { str::from_utf8_unchecked(key) };
        let mut hasher = blake3::Hasher::new_derive_key(key);
        hasher.update(&hash1);
        let mut out = hasher.finalize_xof();
        out.fill(&mut out_hash.0);
        out_hash
    }
}

impl fmt::Debug for Hash160 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Hash160")
            .field(&hex::encode(self.0))
            .finish()
    }
}

#[derive(
    PartialEq,
    Eq,
    Encode,
    Decode,
    Clone,
    HashTrait,
    Zeroize,
    PartialOrd,
    Ord,
    Default,
    Copy,
    Serialize,
    Deserialize,
)]
pub struct Hash256(pub [u8; 32]);

impl Hash256 {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn zero() -> Self {
        Self([0; 32])
    }

    #[inline]
    pub fn hash_from_slice<T: AsRef<[u8]>>(slice: T, key: &str) -> Self {
        let mut out_hash = Hash256([0; 32]);
        let key = &[
            HASH_KEY_PREFIX.as_bytes(),
            HASH_KEY256.as_bytes(),
            ".".as_bytes(),
            key.as_bytes(),
        ]
        .concat();
        let key = unsafe { str::from_utf8_unchecked(key) };
        let mut hasher = blake3::Hasher::new_derive_key(key);
        hasher.update(slice.as_ref());
        let mut out = hasher.finalize_xof();
        out.fill(&mut out_hash.0);
        out_hash
    }

    pub fn meets_difficulty(&self, bits: u32) -> bool {
        let diff = crate::consensus::Difficulty::new(bits);
        let out = crate::consensus::PowOutput::new(self.0);

        out.meets_difficulty(diff)
    }
}

impl From<crate::consensus::PowOutput> for Hash256 {
    fn from(t: crate::consensus::PowOutput) -> Self {
        Self(t.inner())
    }
}

impl AsRef<[u8]> for Hash256 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Hash256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Hash256")
            .field(&hex::encode(self.0))
            .finish()
    }
}

impl Element for Hash256 {
    fn byte_len() -> usize {
        32
    }

    fn from_slice(bytes: &[u8]) -> Self {
        if bytes.len() != Self::byte_len() {
            panic!("invalid slice len")
        }

        let mut out = [0; 32];
        out.copy_from_slice(bytes);
        Self(out)
    }

    fn copy_to_slice(&self, bytes: &mut [u8]) {
        bytes.copy_from_slice(&self.0);
    }
}

impl<H: Hasher> Hashable<H> for Hash256 {
    fn hash(&self, state: &mut H) {
        Hashable::hash(&self.0, state);
    }
}

impl PMMRIndexHashable for Hash256 {
    fn hash_with_index(&self, idx: u64, key: &str) -> Hash256 {
        let to_hash = &[self.0.as_slice(), idx.to_le_bytes().as_slice()].concat();
        Hash256::hash_from_slice(to_hash, key)
    }
}

impl PMMRIndexHashable for (Hash256, Hash256) {
    fn hash_with_index(&self, idx: u64, key: &str) -> Hash256 {
        let to_hash = &[
            self.0 .0.as_slice(),
            self.1 .0.as_slice(),
            idx.to_le_bytes().as_slice(),
        ]
        .concat();
        Hash256::hash_from_slice(to_hash, key)
    }
}

#[derive(Default)]
pub struct Hash256Algo(Vec<u8>);

impl Hasher for Hash256Algo {
    #[inline]
    fn write(&mut self, msg: &[u8]) {
        self.0.extend_from_slice(msg)
    }

    #[inline]
    fn finish(&self) -> u64 {
        unimplemented!()
    }
}

impl Algorithm<Hash256> for Hash256Algo {
    #[inline]
    fn hash(&mut self) -> Hash256 {
        Hash256::hash_from_slice(&self.0, "purplecoin.generichasher.32")
    }

    #[inline]
    fn reset(&mut self) {
        self.0.clear();
    }
}

#[derive(PartialEq, Eq, Encode, Decode, Clone, HashTrait)]
pub struct Hash512(pub [u8; 64]);

impl Hash512 {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn zero() -> Self {
        Self([0; 64])
    }

    pub fn hash_from_slice<T: AsRef<[u8]>>(slice: T, key: &str) -> Self {
        let mut out_hash = Hash512([0; 64]);
        let key = &[
            HASH_KEY_PREFIX.as_bytes(),
            HASH_KEY512.as_bytes(),
            ".".as_bytes(),
            key.as_bytes(),
        ]
        .concat();
        let key = unsafe { str::from_utf8_unchecked(key) };
        let mut hasher = blake3::Hasher::new_derive_key(key);
        hasher.update(slice.as_ref());
        let mut out = hasher.finalize_xof();
        out.fill(&mut out_hash.0);
        out_hash
    }
}

impl fmt::Debug for Hash512 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Hash512")
            .field(&hex::encode(self.0))
            .finish()
    }
}

pub struct AggregatedSignature(PreparedBatch);

impl AggregatedSignature {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(self.0.byte_len());
        self.0.write_bytes(&mut result);
        result
    }
}

impl Encode for AggregatedSignature {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.to_bytes(), encoder)?;
        Ok(())
    }
}

impl Decode for AggregatedSignature {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let sig_bytes: Vec<u8> = bincode::Decode::decode(decoder)?;
        let result = PreparedBatch::read_bytes(&sig_bytes).map_err(|_| {
            bincode::error::DecodeError::OtherString(
                "invalid aggregated signature format".to_owned(),
            )
        })?;
        Ok(Self(result))
    }
}

impl fmt::Debug for AggregatedSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("AggregatedSignature")
            .field(&hex::encode(self.to_bytes()))
            .finish()
    }
}

impl PartialEq for AggregatedSignature {
    fn eq(&self, other: &Self) -> bool {
        self.to_bytes() == other.to_bytes()
    }
}

#[derive(Debug, Clone)]
pub struct BloomFilterHash256 {
    pub inner: Bloom<Hash256>,
}

impl BloomFilterHash256 {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![];
        let bitmap = self.inner.bitmap();
        let bits = self.inner.number_of_bits();
        let num_hashes = self.inner.number_of_hash_functions();
        out.extend_from_slice(&num_hashes.to_le_bytes());
        out.extend_from_slice(&bits.to_le_bytes());
        out.extend_from_slice(&bitmap);
        out
    }

    pub fn from_bytes(bytes: &[u8], sip_keys: [(u64, u64); 2]) -> Result<Self, &'static str> {
        if bytes.len() < 12 {
            return Err("Invalid bytes len, expected at least 12");
        }

        let mut num_bits_buf = [0; 8];
        let mut num_hashes_buf = [0; 4];
        let num_hashes_raw = &bytes[..4];
        let num_bits_raw = &bytes[4..12];
        let bitmap = &bytes[12..];
        num_bits_buf.copy_from_slice(num_bits_raw);
        num_hashes_buf.copy_from_slice(num_hashes_raw);
        let num_bits = u64::from_le_bytes(num_bits_buf);
        let num_hashes = u32::from_le_bytes(num_hashes_buf);

        Ok(Self {
            inner: Bloom::from_existing(bitmap, num_bits, num_hashes, sip_keys),
        })
    }
}

impl PartialEq for BloomFilterHash256 {
    fn eq(&self, other: &Self) -> bool {
        self.inner.sip_keys() == other.inner.sip_keys() && self.to_bytes() == other.to_bytes()
    }
}

impl Eq for BloomFilterHash256 {}

pub trait PMMRIndexHashable {
    fn hash_with_index(&self, idx: u64, key: &str) -> Hash256;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bloom_filter_encode_decode() {
        let seed: [u8; 32] = [0; 32];
        let mut block_bloom = Bloom::new_for_fp_rate_with_seed(
            100,
            crate::consensus::BLOCK_HEADER_BLOOM_FP_RATE,
            &seed,
        );

        for i in 0..100_u8 {
            let hash = Hash256::hash_from_slice([i], "");
            block_bloom.set(&hash);
        }

        let keys = block_bloom.sip_keys();
        let block_bloom = BloomFilterHash256 { inner: block_bloom };

        assert_eq!(
            block_bloom,
            BloomFilterHash256::from_bytes(&block_bloom.to_bytes(), keys).unwrap()
        );
    }
}
