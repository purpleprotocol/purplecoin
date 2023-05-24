// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

fn main() {
    let mut c_build = cc::Build::new();
    let mut cpp_build = cc::Build::new();

    // C build
    c_build.include("c_src/crypto/byteswap");
    c_build.include("c_src/crypto/endian");
    c_build.include("c_src/crypto/common");
    c_build.include("c_src/crypto/md_helper");
    c_build.include("c_src/crypto/sph_types");
    c_build.include("c_src/crypto/sph_fugue");
    c_build.include("c_src/crypto/sph_blake");
    c_build.include("c_src/crypto/sph_bmw");
    c_build.include("c_src/crypto/sph_cubehash");
    c_build.include("c_src/crypto/sph_echo");
    c_build.include("c_src/crypto/sph_groestl");
    c_build.include("c_src/crypto/sph_hamsi");
    c_build.include("c_src/crypto/sph_jh");
    c_build.include("c_src/crypto/sph_keccak");
    c_build.include("c_src/crypto/sph_luffa");
    c_build.include("c_src/crypto/sph_sha2");
    c_build.include("c_src/crypto/sph_shabal");
    c_build.include("c_src/crypto/sph_skein");
    c_build.include("c_src/crypto/sph_simd");
    c_build.include("c_src/crypto/sph_whirlpool");
    c_build.include("c_src/cryptonote/oaes_config");
    c_build.include("c_src/cryptonote/oaes_lib");
    c_build.include("c_src/cryptonote/slow-hash");
    c_build.include("c_src/cryptonote/c_keccak");
    c_build.include("c_src/cryptonote/groestl_tables");
    c_build.include("c_src/cryptonote/c_groestl");
    c_build.include("c_src/cryptonote/c_blake256");
    c_build.include("c_src/cryptonote/c_jh");
    c_build.include("c_src/cryptonote/skein_port");
    c_build.include("c_src/cryptonote/c_skein");
    c_build.include("c_src/cryptonote/int-util");
    c_build.include("c_src/cryptonote/warnings");
    c_build.include("c_src/cryptonote/hash-ops");
    c_build.include("c_src/cryptonote/variant2_int_sqrt");
    c_build.include("c_src/fugue");
    c_build.include("c_src/hash");
    c_build.file("c_src/crypto/sph_fugue.c");
    c_build.file("c_src/crypto/sph_hamsi_helper.c");
    c_build.file("c_src/crypto/sph_hamsi.c");
    c_build.file("c_src/crypto/sph_sha2.c");
    c_build.file("c_src/crypto/sph_sha512.c");
    c_build.file("c_src/crypto/sph_shabal.c");
    c_build.file("c_src/crypto/sph_whirlpool.c");
    c_build.file("c_src/cryptonote/c_keccak.c");
    c_build.file("c_src/cryptonote/c_groestl.c");
    c_build.file("c_src/cryptonote/c_blake256.c");
    c_build.file("c_src/cryptonote/c_jh.c");
    c_build.file("c_src/cryptonote/c_skein.c");
    c_build.file("c_src/cryptonote/hash-ops.c");
    c_build.file("c_src/cryptonote/oaes_lib.c");
    c_build.file("c_src/cryptonote/slow-hash.c");
    c_build.file("c_src/fugue.c");

    c_build.compile("c_hash_sys");

    // C++ build
    cpp_build.include("c_src/crypto/byteswap");
    cpp_build.include("c_src/crypto/endian");
    cpp_build.include("c_src/crypto/common");
    cpp_build.include("c_src/crypto/ripemd160");
    cpp_build.include("c_src/crypto/sha256");
    cpp_build.include("c_src/crypto/sha512");
    cpp_build.include("c_src/crypto/hmac_sha512");
    cpp_build.include("c_src/crypto/sph_types");
    cpp_build.include("c_src/crypto/sph_fugue");
    cpp_build.include("c_src/crypto/sph_blake");
    cpp_build.include("c_src/crypto/sph_bmw");
    cpp_build.include("c_src/crypto/sph_cubehash");
    cpp_build.include("c_src/crypto/sph_echo");
    cpp_build.include("c_src/crypto/sph_groestl");
    cpp_build.include("c_src/crypto/sph_hamsi");
    cpp_build.include("c_src/crypto/sph_jh");
    cpp_build.include("c_src/crypto/sph_keccak");
    cpp_build.include("c_src/crypto/sph_luffa");
    cpp_build.include("c_src/crypto/sph_sha2");
    cpp_build.include("c_src/crypto/sph_shabal");
    cpp_build.include("c_src/crypto/sph_shavite");
    cpp_build.include("c_src/crypto/sph_skein");
    cpp_build.include("c_src/crypto/sph_simd");
    cpp_build.include("c_src/crypto/sph_whirlpool");
    cpp_build.include("c_src/cryptonote/oaes_config");
    cpp_build.include("c_src/cryptonote/oaes_lib");
    cpp_build.include("c_src/cryptonote/slow-hash");
    cpp_build.include("c_src/cryptonote/c_keccak");
    cpp_build.include("c_src/cryptonote/groestl_tables");
    cpp_build.include("c_src/cryptonote/c_groestl");
    cpp_build.include("c_src/cryptonote/c_blake256");
    cpp_build.include("c_src/cryptonote/c_jh");
    cpp_build.include("c_src/cryptonote/skein_port");
    cpp_build.include("c_src/cryptonote/c_skein");
    cpp_build.include("c_src/cryptonote/int-util");
    cpp_build.include("c_src/cryptonote/warnings");
    cpp_build.include("c_src/cryptonote/hash-ops");
    cpp_build.include("c_src/cryptonote/variant2_int_sqrt");
    cpp_build.include("c_src/cryptonote/config");
    cpp_build.include("c_src/cryptonote/stringize");
    cpp_build.include("c_src/utilstrencodings");
    cpp_build.include("c_src/uint256");
    cpp_build.include("c_src/tinyformat");
    cpp_build.include("c_src/version");
    cpp_build.include("c_src/fugue");
    cpp_build.include("c_src/hash_selection");
    cpp_build.include("c_src/hash");
    cpp_build.include("c_src/span");
    cpp_build.include("c_src/compat");
    cpp_build.include("c_src/prevector");
    cpp_build.file("c_src/crypto/ripemd160.cpp");
    cpp_build.file("c_src/crypto/sha256.cpp");
    cpp_build.file("c_src/hash.cpp");

    // Link C library
    println!("cargo:rustc-link-lib=c_hash_sys");

    cpp_build.cpp(true);
    cpp_build.flag_if_supported("-std=c++11");
    cpp_build.compile("hash_sys");
}
