// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use core::ffi::{c_void, c_char};

extern "C" {
    pub fn fugue_hash(input: *const c_char, output: *mut c_char, len: u32) -> *mut c_void;
}