// build.rs

use cmake::Config;
use std::env;

fn main() {
    let dst = Config::new("RandomX").define("DARCH", "native").build();

    println!("cargo:rustc-link-search=native={}/lib", dst.display());
    println!("cargo:rustc-link-lib=static=randomx");

    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or("linux".to_string());

    println!(
        "cargo:rustc-link-lib=dylib={}",
        match target_os.as_str() {
            "openbsd" | "bitrig" | "netbsd" | "macos" | "ios" => {
                "c++"
            }
            _ => "stdc++",
        }
    );
}
