#[cfg(windows)]
const HOST_FAMILY: &str = "windows";

#[cfg(unix)]
const HOST_FAMILY: &str = "unix";

fn main() {
    #[cfg(any(windows, unix))]
    {
        println!("cargo:rust-cfg=host_family={HOST_FAMILY}");
    }

    println!("cargo:rustc-env=CC=clang");
    println!("cargo:rustc-env=CXX=clang++");
}
