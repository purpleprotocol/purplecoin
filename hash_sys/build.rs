// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

fn main() {
    let mut build = cc::Build::new();

    build.include("c_src/sph_types");
    build.include("c_src/sph_fugue");
    build.include("c_src/fugue");
    build.file("c_src/sph_fugue.c");
    build.file("c_src/fugue.c");

    if build.get_compiler().is_like_msvc() {
        build.cpp(true);
    }

    build.compile("sph");
}