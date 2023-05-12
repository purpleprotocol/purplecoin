<!-- Copyright © 2017–2023 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Rust low-level bindings for GMP, MPFR and MPC

The gmp-mpfr-sys crate provides Rust FFI bindings to the following
[GNU] arbitrary-precision libraries:

  * [GMP] for integers and rational numbers,
  * [MPFR] for floating-point numbers, and
  * [MPC] for complex numbers.

The source of the three libraries is included in the package.

The gmp-mpfr-sys crate is free software: you can redistribute it
and/or modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation, either version 3
of the License, or (at your option) any later version. See the full
text of the [GNU LGPL] and [GNU GPL] for details.

## What’s new

### Version 1.5.2 news (2023-03-26)

  * Bug fix: <code>[mpfr][mpfr-1-5]::[pow\_sj][mpfr-ps-1-5]</code> and
    <code>[mpfr][mpfr-1-5]::[pow\_uj][mpfr-pu-1-5]</code> were linking
    to the wrong MPFR function name ([issue 30]).
  * The commits [`0216f40ed..a041c7cbb`] from the [4.2 branch][mpfr 4.2 branch]
    of [MPFR] were merged.

[`0216f40ed..a041c7cbb`]: https://gitlab.inria.fr/mpfr/mpfr/-/compare/0216f40ed...a041c7cbb
[issue 30]: https://gitlab.com/tspiteri/gmp-mpfr-sys/-/issues/30
[mpfr-ps-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.pow_sj.html
[mpfr-pu-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.pow_uj.html

### Version 1.5.1 news (2023-02-28)

  * The commits [`01a3ed526..78ff7526d`] and [`80ea348b3..0216f40ed`] from the [4.2
    branch][mpfr 4.2 branch] of [MPFR] were merged.

[`01a3ed526..78ff7526d`]: https://gitlab.inria.fr/mpfr/mpfr/-/compare/01a3ed526...78ff7526d
[`80ea348b3..0216f40ed`]: https://gitlab.inria.fr/mpfr/mpfr/-/compare/80ea348b3...0216f40ed
[mpfr 4.2 branch]: https://gitlab.inria.fr/mpfr/mpfr/-/tree/4.2

### Version 1.5.0 news (2023-01-06)

  * The crate now requires rustc version 1.65.0 or later.
  * [MPFR] was updated from version 4.1.1-p1 to 4.2.0.
  * [MPC] was updated from version 1.2.1 to 1.3.1.
  * The following functions are now `const` functions:
      * <code>[gmp][gmp-1-5]::[mpz\_sgn][gmp-zs-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpq\_sgn][gmp-qs-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpf\_sgn][gmp-fs-1-5]</code>
      * <code>[gmp][gmp-1-5]::[mpz\_odd\_p][gmp-zop-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpz\_even\_p][gmp-zep-1-5]</code>
      * <code>[gmp][gmp-1-5]::[mpz\_fits\_ulong\_p][gmp-zfulp-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpz\_fits\_uint\_p][gmp-zfuip-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpz\_fits\_ushort\_p][gmp-zfusp-1-5]</code>
      * <code>[gmp][gmp-1-5]::[mpz\_getlimbn][gmp-zg-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpz\_size][gmp-zsi-1-5]</code>,
      * <code>[gmp][gmp-1-5]::[mpq\_numref][gmp-qn-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpq\_numref\_const][gmp-qnc-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpq\_denref][gmp-qd-1-5]</code>,
        <code>[gmp][gmp-1-5]::[mpq\_denref\_const][gmp-qdc-1-5]</code>
      * <code>[mpfr][mpfr-1-5]::[get\_prec][mpfr-gp-1-5]</code>,
      * <code>[mpfr][mpfr-1-5]::[nan\_p][mpfr-nap-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[inf\_p][mpfr-ip-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[number\_p][mpfr-nup-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[zero\_p][mpfr-zp-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[regular\_p][mpfr-rp-1-5]</code>
      * <code>[mpfr][mpfr-1-5]::[get\_exp][mpfr-ge-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[signbit][mpfr-s-1-5]</code>
      * <code>[mpfr][mpfr-1-5]::[VERSION\_NUM][mpfr-vn-1-5]</code>
      * <code>[mpfr][mpfr-1-5]::[custom\_get\_size][mpfr-cgs-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[custom\_init][mpfr-ci-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[custom\_get\_kind][mpfr-cgk-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[custom\_get\_significand][mpfr-cgsi-1-5]</code>,
        <code>[mpfr][mpfr-1-5]::[custom\_get\_exp][mpfr-cge-1-5]</code>
      * <code>[mpc][mpc-1-5]::[INEX\_RE][mpc-ir-1-5]</code>,
        <code>[mpc][mpc-1-5]::[INEX\_IM][mpc-ii-1-5]</code>,
        <code>[mpc][mpc-1-5]::[INEX1][mpc-i1-1-5]</code>,
        <code>[mpc][mpc-1-5]::[INEX2][mpc-i2-1-5]</code>
      * <code>[mpc][mpc-1-5]::[realref][mpc-r-1-5]</code>,
        <code>[mpc][mpc-1-5]::[realref\_const][mpc-rc-1-5]</code>,
        <code>[mpc][mpc-1-5]::[imagref][mpc-i-1-5]</code>,
        <code>[mpc][mpc-1-5]::[imagref\_const][mpc-ic-1-5]</code>
      * <code>[mpc][mpc-1-5]::[VERSION\_NUM][mpc-vn-1-5]</code>
  * The <code>[gmp][gmp-1-5]::[MPZ\_ROINIT\_N][gmp-zrn-1-5]</code> function is
    now `extern "C"`.

[gmp-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/index.html
[gmp-fs-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpf_sgn.html
[gmp-qd-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpq_denref.html
[gmp-qdc-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpq_denref_const.html
[gmp-qn-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpq_numref.html
[gmp-qnc-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpq_numref_const.html
[gmp-qs-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpq_sgn.html
[gmp-zep-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_even_p.html
[gmp-zfuip-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_fits_uint_p.html
[gmp-zfulp-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_fits_ulong_p.html
[gmp-zfusp-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_fits_ushort_p.html
[gmp-zg-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_getlimbn.html
[gmp-zop-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_odd_p.html
[gmp-zrn-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.MPZ_ROINIT_N.html
[gmp-zs-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_sgn.html
[gmp-zsi-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_size.html
[mpc-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/index.html
[mpc-i-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.imagref.html
[mpc-i1-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.INEX1.html
[mpc-i2-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.INEX2.html
[mpc-ic-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.imagref_const.html
[mpc-ii-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.INEX_IM.html
[mpc-ir-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.INEX_RE.html
[mpc-r-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.realref.html
[mpc-rc-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.realref_const.html
[mpc-vn-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/fn.VERSION_NUM.html
[mpfr-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/index.html
[mpfr-cge-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.custom_get_exp.html
[mpfr-cgk-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.custom_get_kind.html
[mpfr-cgs-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.custom_get_size.html
[mpfr-cgsi-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.custom_get_significand.html
[mpfr-ci-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.custom_init.html
[mpfr-ge-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.get_exp.html
[mpfr-gp-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.get_prec.html
[mpfr-ip-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.inf_p.html
[mpfr-nap-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.nan_p.html
[mpfr-nup-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.number_p.html
[mpfr-rp-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.regular_p.html
[mpfr-s-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.signbit.html
[mpfr-vn-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.VERSION_NUM.html
[mpfr-zp-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/fn.zero_p.html

### Other releases

Details on other releases can be found in [*RELEASES.md*].

## Basic features

This crate contains three modules:

  * [`gmp`] provides external FFI bindings to [GMP].
  * [`mpfr`] provides external FFI bindings to [MPFR].
  * [`mpc`] provides external FFI bindings to [MPC].

The versions provided by this crate release are [GMP] version 6.2.1, [MPFR]
version 4.2.0, and [MPC] version 1.3.1.

If you want a high-level API, consider using [Rug][rug crate], a crate
which provides integers and floating-point numbers with arbitrary
precision and correct rounding:

  * [`Integer`] is a bignum integer with arbitrary precision.
  * [`Rational`] is a bignum rational number with arbitrary precision.
  * [`Float`] is a multi-precision floating-point number with correct
    rounding.
  * [`Complex`] is a multi-precision complex number with correct
    rounding.

### Name prefixes

Since modules and enumerated types provide namespacing, most prefixes
in the C names are removed. However, when the prefix is not a whole
word it is not removed. For example [`mp_set_memory_functions`]
becomes [`gmp::set_memory_functions`], but [`mpz_init`] becomes
[`gmp::mpz_init`] not `gmp::z_init`, and [`MPFR_RNDN`] in
[`enum MPFR_RND_T`] becomes [`mpfr::rnd_t::RNDN`] not
`mpfr::rnd_t::N`. Also, the types [`mpfr::mpfr_t`] and [`mpc::mpc_t`]
are *not* shortened to `mpfr::t` or `mpc::t`.

### Types

Unlike in the C libraries, the types [`gmp::mpz_t`], [`gmp::mpq_t`],
[`gmp::mpf_t`], [`gmp::randstate_t`], [`mpfr::mpfr_t`] and
[`mpc::mpc_t`] are defined directly as structs, not as single-element
arrays.

### Undocumented or obsolete functions

The bindings do not cover undocumented or obsolete functions and
macros.

## Using gmp-mpfr-sys

The gmp-mpfr-sys crate is available on [crates.io][sys crate]. To use
gmp-mpfr-sys in your crate, add it as a dependency inside
[*Cargo.toml*]:

```toml
[dependencies]
gmp-mpfr-sys = "1.5"
```

This crate required rustc version 1.65.0 or later.

If the C libraries have a major version bump with some deprecated
functions removed, but no features are removed in the Rust bindings,
then gmp-mpfr-sys will have a minor version bump rather than a major
version bump. This allows more compatiblity across crates that use the
Rust bindings but do not use the C libraries directly.

If on the other hand a dependent crate makes use of internal
implementation details, or includes a C library that directly uses the
header (*.h*) and library (*.a*) files built using C, it can be a good
idea to depend on version `"~1.5"` instead of version `"1.5"` in order
to ensure backwards compatibility at the C level as well.

## Optional features

The gmp-mpfr-sys crate has two optional features:

 1. `mpfr`, enabled by default. Required to include the [MPFR]
    library.
 2. `mpc`, enabled by default. Required to include the [MPC] library.
    This feature requires the `mpfr` feature.

The [GMP] library is always included.

The two optional features are enabled by default; to use features
selectively, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.gmp-mpfr-sys]
version = "1.5"
default-features = false
features = ["mpfr"]
```

Here only the `mpfr` feature is selected.

## Experimental optional features

It is not considered a breaking change if experimental features are
removed. The removal of experimental features would however require a
minor version bump.

Experimental features may also not work on all platforms.

There are three experimental feature:

 1. `use-system-libs`, disabled by default. Using this feature, the
    system libraries for [GMP], and [MPFR] and [MPC] if enabled, will
    be used instead of building them from source. The major versions
    of the system libraries must be equal to those provided by the
    crate, and the minor versions of the system libraries must be
    greater or equal to those provided by the crate. There are no
    restriction on the patch version.
 2. `force-cross`, disabled by default. Without this feature, the
    build will fail if cross compilation is detected, because cross
    compilation is not tested or supported and can lead to silent
    failures that are hard to debug, especially if this crate is an
    indirect dependency. As an exception, cross compiling from x86_64
    to i686 does not need this feature. (Compiling on MinGW does not
    have this exception because MinGW does not support cross
    compilation from 64-bit to 32-bit.)
 3. `c-no-tests`, disabled by default. Using this feature will skip
    testing the C libraries. This is not advised; the risk that the
    GMP sources are miscompiled is unfortunately quite high. And if
    they indeed are miscompiled, the tests are very likely to trigger
    the compiler-introduced bug.

## Metadata

The gmp-mpfr-sys crate passes some metadata to its dependents:

 1. `DEP_GMP_LIMB_BITS` contains the number of bits per limb, which is
    32 or 64.
 2. `DEP_GMP_OUT_DIR` contains the path of a directory that contains
    two subdirectories: the first subdirectory is named *lib* and
    contains the generated library (*.a*) files, and the second
    subdirectory is named *include* and contains the corresponding
    header (*.h*) files.
 3. `DEP_GMP_LIB_DIR` contains the path of the *lib* subdirectory of
    the `DEP_GMP_OUT_DIR` directory.
 4. `DEP_GMP_INCLUDE_DIR` contains the path of the *include*
    subdirectory of the `DEP_GMP_OUT_DIR` directory.

A dependent crate can use these environment variables in its build
script.

## Building on GNU/Linux

To build on GNU/Linux, simply make sure you have `diffutils`, `gcc`,
`m4` and `make` installed on your system. For example on Fedora:

```sh
sudo dnf install diffutils gcc m4 make
```

Note that you can use Clang instead of GCC by installing `clang` and setting the
environment variable `CC=clang` before building the crate.

## Building on macOS

To build on macOS, you need the command-line developer tools. To
install them, run the following command in a terminal:

```sh
xcode-select --install
```

## Building on Windows

You can build on Windows with the Rust GNU toolchain and an up-to-date
MSYS2 installation. Some steps for a 64-bit environment are listed
below. (32-bit: Changes for a 32-bit environment are written in
brackets like this comment.)

To install MSYS2:

 1. Install MSYS2 using the [installer][msys].

 2. Launch the MSYS2 MinGW 64-bit terminal from the start
    menu. (32-bit: Launch the MSYS2 MinGW 32-bit terminal instead.)

 3. Install the required tools.

    ```sh
    pacman -S pacman-mirrors
    pacman -S diffutils m4 make mingw-w64-x86_64-gcc
    ```

    (32-bit: Install `mingw-w64-i686-gcc` instead of
    `mingw-w64-x86_64-gcc`.)

Then, to build a crate with a dependency on this crate:

 1. Launch the MSYS2 MinGW 64-bit terminal from the start menu.
    (32-bit: Launch the MSYS2 MinGW 32-bit terminal instead.)

 2. Change to the crate directory.

 3. Build the crate using `cargo`.

Note that you can use Clang instead of GCC by installing
`mingw-w64-x86_64-clang` (32-bit: `mingw-w64-i686-clang`) and setting the
environment variable `CC=clang` before building the crate.

## Cross compilation

While some cross compilation is possible, it is not tested
automatically, and may not work. Merge requests that improve cross
compilation are accepted.

The experimental feature `force-cross` must be enabled for cross
compilation. There is one case which is allowed even without the
feature: when the only difference between host and target is that the
host is x86_64 and the target is i686.

## Caching the built C libraries

Building the C libraries can take some time. In order to save
compilation time, the built libraries are cached in the user’s cache
directory as follows:

  * on GNU/Linux: inside `$XDG_CACHE_HOME/gmp-mpfr-sys` or
    `$HOME/.cache/gmp-mpfr-sys`
  * on macOS: inside `$HOME/Library/Caches/gmp-mpfr-sys`
  * on Windows: inside `{FOLDERID_LocalAppData}\gmp-mpfr-sys`

To use a different directory, you can set the environment variable
`GMP_MPFR_SYS_CACHE` to the desired cache directory. Setting the
`GMP_MPFR_SYS_CACHE` variable to an empty string or to a single
underscore (`"_"`) will disable caching.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*RELEASES.md*]: https://gitlab.com/tspiteri/gmp-mpfr-sys/blob/master/RELEASES.md
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: https://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Complex`]: https://docs.rs/rug/latest/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/latest/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/latest/rug/struct.Integer.html
[`MPFR_RNDN`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/C/MPFR/constant.MPFR_Basics.html#Rounding-Modes
[`Rational`]: https://docs.rs/rug/latest/rug/struct.Rational.html
[`enum MPFR_RND_T`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/C/MPFR/constant.MPFR_Basics.html#index-mpfr_005frnd_005ft
[`gmp::mpf_t`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/struct.mpf_t.html
[`gmp::mpq_t`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/struct.mpq_t.html
[`gmp::mpz_init`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.mpz_init.html
[`gmp::mpz_t`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/struct.mpz_t.html
[`gmp::randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/struct.randstate_t.html
[`gmp::set_memory_functions`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/fn.set_memory_functions.html
[`gmp`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/gmp/index.html
[`mp_set_memory_functions`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/C/GMP/constant.Custom_Allocation.html#index-mp_005fset_005fmemory_005ffunctions
[`mpc::mpc_t`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/struct.mpc_t.html
[`mpc`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpc/index.html
[`mpfr::mpfr_t`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/struct.mpfr_t.html
[`mpfr::rnd_t::RNDN`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/enum.rnd_t.html#variant.RNDN
[`mpfr`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/mpfr/index.html
[`mpz_init`]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/C/GMP/constant.Integer_Functions.html#index-mpz_005finit
[msys]: https://www.msys2.org/
[rug crate]: https://crates.io/crates/rug
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
