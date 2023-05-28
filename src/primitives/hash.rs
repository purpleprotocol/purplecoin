// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use blake3::Hasher;
use core::ffi::c_char;
use hash_sys::*;

#[inline]
pub fn hash_bytes_fugue256(mut bytes: &[u8]) -> [u8; 32] {
    let mut out: [u8; 32] = [0; 32];
    let data_ptr: *const c_char = &bytes as *const _ as *const c_char;
    let mut out_ptr: *mut c_char = &mut out as *mut _ as *mut c_char;
    unsafe { fugue_hash(data_ptr, out_ptr, bytes.len() as u32) };
    out
}

#[inline]
pub fn hash_bytes_gr(bytes: &[u8; 32], key: [u8; 32]) -> [u8; 32] {
    let mut out: [u8; 32] = [0; 32];
    let data_ptr: *const c_char = bytes as *const _ as *const c_char;
    let key_ptr: *const c_char = &key as *const _ as *const c_char;
    let mut out_ptr: *mut c_char = &mut out as *mut _ as *mut c_char;
    unsafe { gr_hash(data_ptr, key_ptr, out_ptr) };
    out
}

#[inline]
/// As GR receives an input size of 32 bytes we transform an arbitrary
/// sized slice  by hashing it with blake3 prior.
pub fn hash_arb_bytes_gr(bytes: &[u8], key: [u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(bytes);
    let hash = hasher.finalize();
    hash_bytes_gr(hash.as_bytes(), key)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_bytes_fugue256_test() {
        let test_vector = "";
        let result = hash_bytes_fugue256(test_vector.as_bytes());
        let result = hex::encode(result);

        assert_eq!(
            &result,
            "d6ec528980c130aad1d1acd28b9dd8dbdeae0d79eded1fca72c2af9f37c2246f"
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
            "64b9113444feafe614b123e8ad1c0f2b28fe297aefe4a020c83de0807da84eb9"
        );
    }
}
