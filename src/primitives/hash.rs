// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_bytes_fugue256_test() {
        let test_vector = "";
        let result = hash_bytes_fugue256(test_vector.as_bytes());
        let result = hex::encode(&result);

        assert_eq!(
            &result,
            "d6ec528980c130aad1d1acd28b9dd8dbdeae0d79eded1fca72c2af9f37c2246f"
        );
    }
}
