// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use core::ffi::c_void;

extern "C" {
    pub fn fugue_hash(input: *const u8, output: *mut u8, len: u32) -> *mut c_void;
    pub fn gr_hash(input: *const u8, key: *const u8, output: *mut u8) -> *mut c_void;
}
