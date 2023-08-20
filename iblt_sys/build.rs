// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

fn main() {
    println!("cargo:rerun-if-changed=cpp_src");
    let mut cpp_build = cc::Build::new();
    cpp_build.include("cpp_src/murmurhash3");
    cpp_build.include("cpp_src/iblt");
    cpp_build.file("cpp_src/murmurhash3.cpp");
    cpp_build.file("cpp_src/iblt.cpp");
    cpp_build.cpp(true);
    cpp_build.static_crt(true);
    cpp_build.flag_if_supported("-std=c++11");
    cpp_build.compile("iblt_sys");
    println!("cargo:rustc-link-lib=static=iblt_sys");
}
