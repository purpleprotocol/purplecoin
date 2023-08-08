## Build instructions
This document describes how to build Purplecoin on different platforms. Purplecoin is built daily against nightly Rust so installing the latest nightly version should always work.

### Linux Debian
Asuming Ubuntu/Debian, run the following:
```
sudo apt-get update -y
sudo apt-get install -y make g++ m4 cmake clang libclang-dev openssl zlib1g-dev llvm llvm-dev xutils-dev autoconf autoconf-archive automake libc-dev linux-libc-dev build-essential pkgconf curl
```

Install the Rust toolchain:
```
curl https://sh.rustup.rs -sSf | sh -s -- --default-toolchain nightly -y
```

Then run:
```
cargo build
```

### Macos
Install llvm and m4:
```
brew install llvm m4
```

Install the Rust toolchain:
```
curl https://sh.rustup.rs -sSf | sh -s -- --default-toolchain nightly -y
```

Then run:
```
cargo build
```


### Windows
Building on Windows doesn't work on msvc and requires msys2. 

Building should be done in the msys2 shell. Install the required packages by running the following inside the msys2 shell:
```
pacman -S curl diffutils base-devel make mingw-w64-x86_64-clang cmake m4
```

Install the correct Rust toolchain:
```
curl https://sh.rustup.rs -sSf | sh -s -- --default-toolchain nightly-x86_64-pc-windows-gnu -y
```

Then inside the msys2 shell:
```
cargo build
```
