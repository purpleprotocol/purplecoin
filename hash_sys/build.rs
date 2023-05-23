// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

fn main() {
    let mut build = cc::Build::new();

    build.include("c_src/crypto/sph_types");
    build.include("c_src/crypto/sph_fugue");
    build.include("c_src/cryptonote/oaes_lib");
    build.include("c_src/cryptonote/slow-hash");
    build.include("c_src/cryptonote/c_keccak");
    build.include("c_src/cryptonote/c_groestl");
    build.include("c_src/cryptonote/c_blake256");
    build.include("c_src/cryptonote/c_jh");
    build.include("c_src/cryptonote/c_skein");
    build.include("c_src/cryptonote/int-util");
    build.include("c_src/cryptonote/warnings");
    build.include("c_src/cryptonote/hash-ops");
    build.include("c_src/cryptonote/variant2_int_sqrt");
    build.include("c_src/fugue");
    build.include("c_src/hash_selection");
    build.include("c_src/hash");
    build.file("c_src/crypto/sph_fugue.c");
    build.file("c_src/cryptonote/c_keccak.c");
    build.file("c_src/cryptonote/c_groestl.c");
    build.file("c_src/cryptonote/c_blake256.c");
    build.file("c_src/cryptonote/c_jh.c");
    build.file("c_src/cryptonote/c_skein.c");
    build.file("c_src/cryptonote/hash-ops.c");
    build.file("c_src/cryptonote/oaes_lib.c");
    build.file("c_src/cryptonote/slow-hash.c");
    build.file("c_src/fugue.c");
    build.file("c_src/hash.cpp");

    build.cpp(true);
    build.compile("hash_sys");
}
