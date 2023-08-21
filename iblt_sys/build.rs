// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=cpp_src");
    let mut cpp_build = cc::Build::new();
    cpp_build.include("cpp_src/murmurhash3");
    cpp_build.include("cpp_src/iblt");
    cpp_build.file("cpp_src/murmurhash3.cpp");
    cpp_build.file("cpp_src/iblt.cpp");
    cpp_build.cpp(true);
    cpp_build.static_crt(true);
    cpp_build.flag_if_supported("-std=c++17");
    cpp_build.compile("iblt_sys");
    println!("cargo:rustc-link-lib=static=iblt_sys");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    let bindings = bindgen::Builder::default()
        .header("./cpp_src/iblt.h")
        // Not generate the layout test code
        .layout_tests(false)
        // Not derive `Debug, Clone, Copy, Default` trait by default
        .derive_debug(false)
        .derive_copy(false)
        .derive_default(false)
        // Enable C++ namespace support
        .enable_cxx_namespaces()
        // Add extra clang args for supporting `C++`
        .clang_arg("-x")
        .clang_arg("c++")
        .clang_arg("-std=c++17")
        .clang_arg("-stdlib=libc++")
        // Opaque types
        .opaque_type("std_.*")
        .opaque_type("std::tuple_.*")
        .opaque_type("std::tuple")
        // Blocked types
        .blocklist_item("std::value")
        .blocklist_item("List_iterator")
        .blocklist_type("std::char_traits")
        .blocklist_item("std_basic_string")
        .blocklist_item("std_collate.*")
        .blocklist_item("__gnu_cxx__min")
        // Tell cargo to invalidate the built crate whenever any of the
        // included header files changed.
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        // Block types
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    bindings
        .write_to_file(out_path.clone().join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // Fix bindings as duplicates are being generated
    let mut file = File::open(out_path.join("bindings.rs")).expect("file error");
    let reader = BufReader::new(&mut file);

    let mut lines: Vec<_> = reader
        .lines()
        .map(|l| l.expect("Couldn't read a line"))
        // Fix lines
        .filter_map(|l| {
            if l.contains("pub type __memory_order_underlying_t = root::type_;") {
                return Some(l.replace(
                    "pub type __memory_order_underlying_t = root::type_;",
                    "pub type __memory_order_underlying_t = root::memory_type_;",
                ));
            }

            if l.contains("pub type type_ = ::std::os::raw::c_uint;") {
                return Some(l.replace("type_", "memory_type_"));
            }

            if l.contains("pub type _IsCharLikeType = root::std::_And<_Pred>;")
                || l.contains(
                    "pub type __enable_hash_helper = root::std::__enable_hash_helper_imp<_Type>;",
                )
            {
                return None;
            }

            Some(l)
        })
        .collect();
    lines.dedup();

    let mut file = File::create(out_path.join("bindings.rs")).expect("file error");

    for line in lines {
        file.write_all(line.as_bytes())
            .expect("Couldn't write to file");
        file.write_all("\n".as_bytes())
            .expect("Couldn't write to file");
    }
}
