// Copyright © 2016–2022 Trevor Spiteri

// Copying and distribution of this file, with or without modification, are
// permitted in any medium without royalty provided the copyright notice and
// this notice are preserved. This file is offered as-is, without any warranty.

#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]

use std::{
    env,
    ffi::OsString,
    fs::{self, File},
    io::{Result as IoResult, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

fn main() {
    if env::var_os("CARGO_FEATURE_GMP_MPFR_SYS").is_some() {
        let bits =
            env::var_os("DEP_GMP_LIMB_BITS").expect("DEP_GMP_LIMB_BITS not set by gmp-mfpr-sys");
        let bits = bits
            .to_str()
            .expect("DEP_GMP_LIMB_BITS contains unexpected characters");
        if bits != "32" && bits != "64" {
            panic!("Limb bits not 32 or 64: \"{}\"", bits);
        }
        println!("cargo:rustc-cfg=gmp_limb_bits_{}", bits);
    }

    check_feature("unsafe_in_unsafe", TRY_UNSAFE_IN_UNSAFE);
}

fn check_feature(name: &str, contents: &str) {
    let rustc = cargo_env("RUSTC");
    let out_dir = PathBuf::from(cargo_env("OUT_DIR"));

    let try_dir = out_dir.join(format!("try_{}", name));
    let filename = format!("try_{}.rs", name);
    create_dir_or_panic(&try_dir);
    println!("$ cd {:?}", try_dir);
    create_file_or_panic(&try_dir.join(&filename), contents);
    let mut cmd = Command::new(&rustc);
    cmd.current_dir(&try_dir)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .args(&[&*filename, "--emit=dep-info,metadata"]);
    println!("$ {:?} >& /dev/null", cmd);
    let status = cmd
        .status()
        .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
    if status.success() {
        println!("cargo:rustc-cfg={}", name);
    }
    remove_dir_or_panic(&try_dir);
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name)
        .unwrap_or_else(|| panic!("environment variable not found: {}, please use cargo", name))
}

fn remove_dir(dir: &Path) -> IoResult<()> {
    if !dir.exists() {
        return Ok(());
    }
    assert!(dir.is_dir(), "Not a directory: {:?}", dir);
    println!("$ rm -r {:?}", dir);
    fs::remove_dir_all(dir)
}

fn remove_dir_or_panic(dir: &Path) {
    remove_dir(dir).unwrap_or_else(|_| panic!("Unable to remove directory: {:?}", dir));
}

fn create_dir(dir: &Path) -> IoResult<()> {
    println!("$ mkdir -p {:?}", dir);
    fs::create_dir_all(dir)
}

fn create_dir_or_panic(dir: &Path) {
    create_dir(dir).unwrap_or_else(|_| panic!("Unable to create directory: {:?}", dir));
}

fn create_file_or_panic(filename: &Path, contents: &str) {
    println!("$ printf '%s' {:?}... > {:?}", &contents[0..10], filename);
    let mut file =
        File::create(filename).unwrap_or_else(|_| panic!("Unable to create file: {:?}", filename));
    file.write_all(contents.as_bytes())
        .unwrap_or_else(|_| panic!("Unable to write to file: {:?}", filename));
}

const TRY_UNSAFE_IN_UNSAFE: &str = r#"// try_unsafe_in_unsafe.rs
#![deny(unknown_lints)]
#![warn(unsafe_op_in_unsafe_fn)]

fn main() {}
"#;
