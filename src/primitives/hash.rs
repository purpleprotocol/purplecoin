// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

#![allow(clippy::all, clippy::pedantic, clippy::restriction, clippy::nursery)]

use blake2::digest::{Update, VariableOutput};
use blake2::Blake2bVar;
use core::ffi::c_char;
use hash_sys::{fugue_hash, gr_hash};

#[inline]
#[must_use]
pub fn hash_bytes_fugue256(mut bytes: &[u8]) -> [u8; 32] {
    let mut out: [u8; 32] = [0; 32];
    unsafe { fugue_hash(bytes.as_ptr(), out.as_mut_ptr(), bytes.len() as u32) };
    out
}

#[inline]
#[must_use]
pub fn hash_bytes_gr(bytes: &[u8; 32], key: [u8; 32]) -> [u8; 32] {
    let mut out: [u8; 32] = [0; 32];
    unsafe { gr_hash(bytes.as_ptr(), key.as_ptr(), out.as_mut_ptr()) };
    out
}

#[inline]
/// As GR receives an input size of 32 bytes we transform an arbitrary
/// sized slice by hashing it with blake2b prior.
#[must_use]
pub fn hash_arb_bytes_gr(bytes: &[u8], key: [u8; 32]) -> [u8; 32] {
    let mut hasher = Blake2bVar::new(32).unwrap();
    let mut buf = [0u8; 32];
    hasher.update(bytes);
    hasher.finalize_variable(&mut buf).unwrap();
    hash_bytes_gr(&buf, key)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_bytes_fugue256_test_1() {
        let result = hash_bytes_fugue256(&[]);
        let result = hex::encode(result);
        let result2 = hash_bytes_fugue256(&[]);
        let result2 = hex::encode(result2);

        assert_eq!(
            &result,
            "d6ec528980c130aad1d1acd28b9dd8dbdeae0d79eded1fca72c2af9f37c2246f"
        );
        assert_eq!(
            &result2,
            "d6ec528980c130aad1d1acd28b9dd8dbdeae0d79eded1fca72c2af9f37c2246f"
        );
    }

    #[test]
    fn hash_bytes_fugue256_test_2() {
        let result = hash_bytes_fugue256(&[0x4a, 0x4f, 0x20, 0x24, 0x84, 0x51, 0x25, 0x26]);
        let result = hex::encode(result);
        let result2 = hash_bytes_fugue256(&[0x4a, 0x4f, 0x20, 0x24, 0x84, 0x51, 0x25, 0x26]);
        let result2 = hex::encode(result2);

        assert_eq!(
            &result,
            "84e8df742af4ab3f552a148485a1d27943b57ba748b76a1cdf8e1f054bed3d7b"
        );
        assert_eq!(
            &result2,
            "84e8df742af4ab3f552a148485a1d27943b57ba748b76a1cdf8e1f054bed3d7b"
        );
    }

    #[test]
    fn hash_bytes_fugue256_test_3() {
        let result = hash_bytes_fugue256(&[
            0x5b, 0xe4, 0x3c, 0x90, 0xf2, 0x29, 0x02, 0xe4, 0xfe, 0x8e, 0xd2, 0xd3,
        ]);
        let result = hex::encode(result);
        let result2 = hash_bytes_fugue256(&[
            0x5b, 0xe4, 0x3c, 0x90, 0xf2, 0x29, 0x02, 0xe4, 0xfe, 0x8e, 0xd2, 0xd3,
        ]);
        let result2 = hex::encode(result2);

        assert_eq!(
            &result,
            "d94c33e8312522b6393ebdfb4c99137265c8965782e4d7b4495640bfd6a75760"
        );
        assert_eq!(
            &result2,
            "d94c33e8312522b6393ebdfb4c99137265c8965782e4d7b4495640bfd6a75760"
        );
    }

    #[test]
    fn hash_bytes_gr_test() {
        let result = hash_bytes_gr(&[0; 32], [0; 32]);
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "30509701abd90d57fc7ace37cfb4cb51a45632053c2af45e52d89a297fdeef62"
        );
    }

    #[test]
    fn hash_bytes_arb_gr_test() {
        let result = hash_arb_bytes_gr(&[0; 32], [0; 32]);
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "98bfff347e50a5d105893ea0961d32148a7c572bf0d663dc980849fe95f2e2c5"
        );
    }

    #[test]
    fn hash_bytes_gr_test_2() {
        let result = hash_bytes_gr(&[0xcc; 32], [0; 32]);
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "17b96b01f6b9cc11d744940eb14d1886066ebd6954c3a5bd7878fd05cc2cee80"
        );
    }

    #[test]
    fn hash_bytes_arb_gr_test_2() {
        let result = hash_arb_bytes_gr(&[0xcc; 32], [0; 32]);
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "4998754b8c97df7fd652961fef096088ca7f49e3a52e88669d2ee55b19959478"
        );
    }

    #[test]
    fn hash_bytes_gr_test_3() {
        let result = hash_bytes_gr(&[0xcc; 32], [0x05; 32]);
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "d67a9f43c4d3f89be3bb410e4e8f4321b3f91c25658d674801dfb2bb34fef749"
        );
    }

    #[test]
    fn hash_bytes_arb_gr_test_3() {
        let result = hash_arb_bytes_gr(&[0xcc; 32], [0x05; 32]);
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "990afd3ccdca562bf8b5d0d9cd0a52482395d4a48cdad4be1d34b2ca5b4d25e0"
        );
    }
}
