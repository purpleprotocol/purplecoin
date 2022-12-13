// Copyright © 2017–2022 Trevor Spiteri

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <https://www.gnu.org/licenses/>.

/*!
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

## Basic features

This crate contains three modules:

  * [`gmp`] provides external FFI bindings to [GMP].
  * [`mpfr`] provides external FFI bindings to [MPFR].
  * [`mpc`] provides external FFI bindings to [MPC].

The versions provided by this crate release are [GMP] version 6.2.1,
[MPFR] version 4.1.0-p13, and [MPC] version 1.2.1.

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
gmp-mpfr-sys = "1.4"
```

This crate required rustc version 1.37.0 or later.

If the C libraries have a major version bump with some deprecated
functions removed, but no features are removed in the Rust bindings,
then gmp-mpfr-sys will have a minor version bump rather than a major
version bump. This allows more compatiblity across crates that use the
Rust bindings but do not use the C libraries directly.

If on the other hand a dependent crate makes use of internal
implementation details, or includes a C library that directly uses the
header (*.h*) and library (*.a*) files built using C, it can be a good
idea to depend on version `"~1.4"` instead of version `"1.4"` in order
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
version = "1.4"
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

Note that you can use Clang instead of GCC by installing `clang` instead of
`gcc` and setting the environment variable `CC=clang` before building the crate.

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
underscore (`"_"`)  will disable caching.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Complex`]: https://docs.rs/rug/&#42;/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/&#42;/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/&#42;/rug/struct.Integer.html
[`MPFR_RNDN`]: C/MPFR/constant.MPFR_Basics.html#Rounding-Modes
[`Rational`]: https://docs.rs/rug/&#42;/rug/struct.Rational.html
[`enum MPFR_RND_T`]: C/MPFR/constant.MPFR_Basics.html#index-mpfr_005frnd_005ft
[`mp_set_memory_functions`]: C/GMP/constant.Custom_Allocation.html#index-mp_005fset_005fmemory_005ffunctions
[`mpz_init`]: C/GMP/constant.Integer_Functions.html#index-mpz_005finit
[msys]: https://www.msys2.org/
[rug crate]: https://crates.io/crates/rug
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/gmp-mpfr-sys/~1.4")]
#![doc(html_logo_url = "data:image/svg+xml;base64,
PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0iVVRGLTgiPz4KPCEtLSBDcmVhdGVkIHdpdGggSW5rc2NhcGUgKGh0dHA6Ly93
d3cuaW5rc2NhcGUub3JnLykgLS0+Cjxzdmcgd2lkdGg9IjEyOCIgaGVpZ2h0PSIxMjgiIHZlcnNpb249IjEuMSIgdmlld0JveD0i
MCAwIDMzLjg2NyAzMy44NjciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgeG1sbnM6Y2M9Imh0dHA6Ly9jcmVh
dGl2ZWNvbW1vbnMub3JnL25zIyIgeG1sbnM6ZGM9Imh0dHA6Ly9wdXJsLm9yZy9kYy9lbGVtZW50cy8xLjEvIiB4bWxuczpyZGY9
Imh0dHA6Ly93d3cudzMub3JnLzE5OTkvMDIvMjItcmRmLXN5bnRheC1ucyMiPgogPG1ldGFkYXRhPgogIDxyZGY6UkRGPgogICA8
Y2M6V29yayByZGY6YWJvdXQ9IiI+CiAgICA8ZGM6Zm9ybWF0PmltYWdlL3N2Zyt4bWw8L2RjOmZvcm1hdD4KICAgIDxkYzp0eXBl
IHJkZjpyZXNvdXJjZT0iaHR0cDovL3B1cmwub3JnL2RjL2RjbWl0eXBlL1N0aWxsSW1hZ2UiLz4KICAgPC9jYzpXb3JrPgogIDwv
cmRmOlJERj4KIDwvbWV0YWRhdGE+CiA8ZyB0cmFuc2Zvcm09InRyYW5zbGF0ZSgwIC0yNjMuMTMpIj4KICA8Y2lyY2xlIGN4PSIx
Ni45MzMiIGN5PSIyODAuMDciIHI9IjE2LjkzMyIgZmlsbD0iI2Y3ZjFhMSIvPgogIDxnIGZpbGw9IiMwMDcyYjIiIHN0cm9rZS13
aWR0aD0iLjI2NDU4cHgiPgogICA8ZyBzdHJva2U9IiMwMDAiPgogICAgPGcgYXJpYS1sYWJlbD0iNiI+CiAgICAgPHBhdGggZD0i
bTE0LjM2MSAyNzguNzFjMC42NjA0IDAgMS4yODQxIDAuMjc1MTYgMS4yODQxIDEuMzk0MiAwIDEuMjI5MS0wLjU4NzAyIDEuNjE0
My0xLjI0NzQgMS42MTQzLTAuNTY4NjggMC0xLjI2NTgtMC4zODUyMy0xLjUyMjYtMi4wMTc5IDAuMzY2ODktMC42OTcwOSAwLjkz
NTU2LTAuOTkwNiAxLjQ4NTktMC45OTA2em0wLjExMDA3IDUuMzU2NmMyLjIwMTMgMCA0LjAzNTgtMS40Njc2IDQuMDM1OC0zLjk2
MjRzLTEuNTQwOS0zLjU5NTUtMy41MjIxLTMuNTk1NWMtMC42MjM3MSAwLTEuNjE0MyAwLjQwMzU4LTIuMTgzIDEuMTU1NyAwLjEy
ODQxLTIuMzQ4MSAxLjAwODktMy4xMzY5IDIuMTQ2My0zLjEzNjkgMC42NjA0IDAgMS4zOTQyIDAuNDAzNTcgMS43NjExIDAuODA3
MTVsMS42NTEtMS44NzExYy0wLjc3MDQ2LTAuNzcwNDYtMS45ODEyLTEuNDY3Ni0zLjYzMjItMS40Njc2LTIuNDk0OCAwLTQuODA2
MiAyLjAxNzktNC44MDYyIDYuMjM3MSAwIDQuMjE5MiAyLjMxMTQgNS44MzM1IDQuNTQ5NCA1LjgzMzV6IiBzdHJva2U9Im5vbmUi
Lz4KICAgIDwvZz4KICAgIDxnIHRyYW5zZm9ybT0icm90YXRlKDE1LjUxNSkiIGFyaWEtbGFiZWw9IjIiPgogICAgIDxwYXRoIGQ9
Im05OC4wMjggMjY3Ljk1aDUuMDQ2MXYtMS4zOTk4aC0xLjYwM2MtMC4zMjczOCAwLTAuODI0MDkgMC4wNDUxLTEuMTk2NiAwLjA5
MDMgMS4yNzU2LTEuMjUzMSAyLjQ0OTctMi40MjcxIDIuNDQ5Ny0zLjcyNTMgMC0xLjM2Ni0wLjk1OTU2LTIuMjY5MS0yLjM3MDct
Mi4yNjkxLTEuMDA0NyAwLTEuNjgyIDAuMzk1MTEtMi4zNzA3IDEuMTc0bDAuODY5MjQgMC44NTc5NmMwLjM2MTI0LTAuMzgzODMg
MC43NTYzNi0wLjczMzc4IDEuMjc1Ni0wLjczMzc4IDAuNjIwODkgMCAxLjAxNiAwLjM4MzgyIDEuMDE2IDEuMDgzNyAwIDEuMDA0
Ny0xLjMwOTUgMi4yOTE2LTMuMTE1NyAzLjg5NDd6IiBmaWxsLW9wYWNpdHk9Ii45NzI1NSIgc3Ryb2tlPSJub25lIi8+CiAgICA8
L2c+CiAgICA8ZyB0cmFuc2Zvcm09InJvdGF0ZSgtMTEuMDMzKSIgYXJpYS1sYWJlbD0iOCI+CiAgICAgPHBhdGggZD0ibS0zOC45
MiAyOTAuNzZjMS4yNzQyIDAgMi4xMjM3LTAuNzQwODMgMi4xMjM3LTEuNzA4OCAwLTAuODM5NjItMC41MDM3Ny0xLjMwMzktMS4w
ODY2LTEuNjI5OHYtMC4wMzk1YzAuNDA0OTktMC4yOTYzMyAwLjgzOTYxLTAuODE5ODYgMC44Mzk2MS0xLjQ0MjIgMC0xLjAxNzQt
MC43MjEwOC0xLjY5OS0xLjg0NzEtMS42OTktMS4wODY2IDAtMS44OTY1IDAuNjUxOTMtMS44OTY1IDEuNjY5MyAwIDAuNjYxODEg
MC4zODUyMyAxLjEyNjEgMC44NjkyNCAxLjQ3MTh2MC4wMzk1Yy0wLjU5MjY3IDAuMzE2MDktMS4xMzU5IDAuODI5NzQtMS4xMzU5
IDEuNjEwMSAwIDEuMDE3NCAwLjkwODc2IDEuNzI4NiAyLjEzMzYgMS43Mjg2em0wLjQxNDg3LTMuNjY0N2MtMC43MDEzMi0wLjI3
NjU3LTEuMjY0NC0wLjU1MzE1LTEuMjY0NC0xLjE4NTMgMC0wLjU0MzI4IDAuMzc1MzYtMC44NTkzNyAwLjg1OTM3LTAuODU5Mzcg
MC41ODI3OSAwIDAuOTI4NTEgMC40MDQ5OSAwLjkyODUxIDAuOTU4MTUgMCAwLjM5NTExLTAuMTg3NjggMC43NTA3MS0wLjUyMzUy
IDEuMDg2NnptLTAuMzk1MTEgMi44NTQ3Yy0wLjY0MjA2IDAtMS4xNTU3LTAuNDE0ODYtMS4xNTU3LTEuMDM3MiAwLTAuNDg0MDEg
MC4yODY0Ni0wLjg4OSAwLjY4MTU3LTEuMTc1NSAwLjg0OTQ5IDAuMzQ1NzIgMS41MTEzIDAuNTkyNjcgMS41MTEzIDEuMjc0MiAw
IDAuNTgyNzktMC40MzQ2MiAwLjkzODM5LTEuMDM3MiAwLjkzODM5eiIgZmlsbC1vcGFjaXR5PSIuOTQxMTgiIHN0cm9rZT0ibm9u
ZSIvPgogICAgPC9nPgogICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoNi41MDA4KSIgYXJpYS1sYWJlbD0iMyI+CiAgICAgPHBhdGgg
ZD0ibTM5LjMwMiAyODMuNjRjMS4wMzI5IDAgMS44ODgxLTAuNTc1NzMgMS44ODgxLTEuNTU3OSAwLTAuNzExMi0wLjQ4MjYtMS4x
Njg0LTEuMTE3Ni0xLjMzNzd2LTAuMDMzOWMwLjU4NDItMC4yMjg2IDAuOTM5OC0wLjYzNSAwLjkzOTgtMS4yMzYxIDAtMC45MTQ0
LTAuNzExMi0xLjQyMjQtMS43NDQxLTEuNDIyNC0wLjY0MzQ3IDAtMS4xNTk5IDAuMjcwOTMtMS42MTcxIDAuNjc3MzNsMC40OTk1
MyAwLjYwMTE0YzAuMzMwMi0wLjMwNDggMC42NjA0LTAuNTA4IDEuMDgzNy0wLjUwOCAwLjQ5MTA3IDAgMC43OTU4NyAwLjI3MDkz
IDAuNzk1ODcgMC43MTk2NiAwIDAuNDk5NTQtMC4zNDcxMyAwLjg2MzYtMS40MDU1IDAuODYzNnYwLjcxMTJjMS4yMjc3IDAgMS41
ODMzIDAuMzU1NiAxLjU4MzMgMC45MTQ0IDAgMC41MDgtMC40MDY0IDAuODEyODEtMC45OTA2IDAuODEyODEtMC41NDE4NyAwLTAu
OTU2NzMtMC4yNjI0Ny0xLjI3ODUtMC41OTI2N2wtMC40NjU2NyAwLjYyNjUzYzAuMzgxIDAuNDIzMzQgMC45NTY3MyAwLjc2MiAx
LjgyODggMC43NjJ6IiBmaWxsLW9wYWNpdHk9Ii44Nzg0MyIgc3Ryb2tlPSJub25lIi8+CiAgICA8L2c+CiAgICA8ZyB0cmFuc2Zv
cm09InJvdGF0ZSg4LjM1NikiIGFyaWEtbGFiZWw9IjEiPgogICAgIDxwYXRoIGQ9Im00Ni40MDUgMjY4LjloMy4yNDI3di0wLjc5
NTg3aC0xLjA1ODN2LTQuNTg4OWgtMC43MjgxM2MtMC4zMzg2NyAwLjIwMzItMC43MTEyIDAuMzM4NjctMS4yNDQ2IDAuNDQwMjd2
MC42MDk2aDAuOTkwNnYzLjUzOTFoLTEuMjAyM3oiIGZpbGwtb3BhY2l0eT0iLjc1Mjk0IiBzdHJva2U9Im5vbmUiLz4KICAgIDwv
Zz4KICAgIDxnIHRyYW5zZm9ybT0icm90YXRlKDEyLjg2MSkiIGFyaWEtbGFiZWw9IjgiPgogICAgIDxwYXRoIGQ9Im04NS4wMzYg
MjYxLjYzYzEuMDkyMiAwIDEuODIwMy0wLjYzNSAxLjgyMDMtMS40NjQ3IDAtMC43MTk2Ny0wLjQzMTgtMS4xMTc2LTAuOTMxMzMt
MS4zOTd2LTAuMDMzOWMwLjM0NzEzLTAuMjU0IDAuNzE5NjctMC43MDI3MyAwLjcxOTY3LTEuMjM2MSAwLTAuODcyMDctMC42MTgw
Ny0xLjQ1NjMtMS41ODMzLTEuNDU2My0wLjkzMTMzIDAtMS42MjU2IDAuNTU4OC0xLjYyNTYgMS40MzA5IDAgMC41NjcyNiAwLjMz
MDIgMC45NjUyIDAuNzQ1MDcgMS4yNjE1djAuMDMzOWMtMC41MDggMC4yNzA5My0wLjk3MzY3IDAuNzExMi0wLjk3MzY3IDEuMzgw
MSAwIDAuODcyMDcgMC43Nzg5MyAxLjQ4MTcgMS44Mjg4IDEuNDgxN3ptMC4zNTU2LTMuMTQxMWMtMC42MDExMy0wLjIzNzA3LTEu
MDgzNy0wLjQ3NDE0LTEuMDgzNy0xLjAxNiAwLTAuNDY1NjcgMC4zMjE3My0wLjczNjYgMC43MzY2LTAuNzM2NiAwLjQ5OTUzIDAg
MC43OTU4NyAwLjM0NzEzIDAuNzk1ODcgMC44MjEyNiAwIDAuMzM4NjctMC4xNjA4NyAwLjY0MzQ3LTAuNDQ4NzMgMC45MzEzNHpt
LTAuMzM4NjcgMi40NDY5Yy0wLjU1MDMzIDAtMC45OTA2LTAuMzU1Ni0wLjk5MDYtMC44ODkgMC0wLjQxNDg2IDAuMjQ1NTMtMC43
NjIgMC41ODQyLTEuMDA3NSAwLjcyODEzIDAuMjk2MzMgMS4yOTU0IDAuNTA4IDEuMjk1NCAxLjA5MjIgMCAwLjQ5OTUzLTAuMzcy
NTMgMC44MDQzMy0wLjg4OSAwLjgwNDMzeiIgZmlsbC1vcGFjaXR5PSIuNjI3NDUiIHN0cm9rZT0ibm9uZSIvPgogICAgPC9nPgog
ICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoNC4zMDk5KSIgYXJpYS1sYWJlbD0iNSI+CiAgICAgPHBhdGggZD0ibTQ2LjM0MSAyODku
NDljMC45OTA2IDAgMS44OTY1LTAuNjc3MzQgMS44OTY1LTEuODU0MiAwLTEuMTU5OS0wLjc3MDQ3LTEuNjg0OS0xLjY5MzMtMS42
ODQ5LTAuMjc5NCAwLTAuNDgyNiAwLjA2NzctMC43MTEyIDAuMTc3OGwwLjExMDA3LTEuMzAzOWgyLjAzMnYtMC44MjEyN2gtMi44
Nzg3bC0wLjE2MDg3IDIuNjU4NSAwLjQ2NTY3IDAuMjk2MzNjMC4zMjE3My0wLjIxMTY3IDAuNTE2NDctMC4zMDQ4IDAuODYzNi0w
LjMwNDggMC41OTI2NyAwIDAuOTkwNiAwLjM2NDA3IDAuOTkwNiAxLjAwNzUgMCAwLjY1MTk0LTAuNDQwMjcgMS4wMzI5LTEuMDQx
NCAxLjAzMjktMC41NDE4NyAwLTAuOTM5OC0wLjI3MDk0LTEuMjYxNS0wLjU3NTc0bC0wLjQ0ODczIDAuNjI2NTRjMC4zOTc5MyAw
LjM5NzkzIDAuOTY1MiAwLjc0NTA3IDEuODM3MyAwLjc0NTA3eiIgZmlsbC1vcGFjaXR5PSIuNTAxOTYiIHN0cm9rZT0ibm9uZSIv
PgogICAgPC9nPgogICAgPGcgZmlsbC1vcGFjaXR5PSIuMzc2NDciIGFyaWEtbGFiZWw9IjMiPgogICAgIDxwYXRoIGQ9Im05Ljg4
NTkgMjkzLjQ2YzEuMDMyOSAwIDEuODg4MS0wLjU3NTc0IDEuODg4MS0xLjU1NzkgMC0wLjcxMTItMC40ODI2LTEuMTY4NC0xLjEx
NzYtMS4zMzc3di0wLjAzMzljMC41ODQyLTAuMjI4NiAwLjkzOTgtMC42MzUgMC45Mzk4LTEuMjM2MSAwLTAuOTE0NC0wLjcxMTIt
MS40MjI0LTEuNzQ0MS0xLjQyMjQtMC42NDM0NyAwLTEuMTU5OSAwLjI3MDk0LTEuNjE3MSAwLjY3NzM0bDAuNDk5NTMgMC42MDEx
M2MwLjMzMDItMC4zMDQ4IDAuNjYwNC0wLjUwOCAxLjA4MzctMC41MDggMC40OTEwNyAwIDAuNzk1ODcgMC4yNzA5MyAwLjc5NTg3
IDAuNzE5NjcgMCAwLjQ5OTUzLTAuMzQ3MTMgMC44NjM2LTEuNDA1NSAwLjg2MzZ2MC43MTEyYzEuMjI3NyAwIDEuNTgzMyAwLjM1
NTYgMS41ODMzIDAuOTE0NCAwIDAuNTA4LTAuNDA2NCAwLjgxMjgtMC45OTA2IDAuODEyOC0wLjU0MTg3IDAtMC45NTY3My0wLjI2
MjQ3LTEuMjc4NS0wLjU5MjY3bC0wLjQ2NTY3IDAuNjI2NTRjMC4zODEgMC40MjMzMyAwLjk1NjczIDAuNzYyIDEuODI4OCAwLjc2
MnoiIHN0cm9rZT0ibm9uZSIvPgogICAgPC9nPgogICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoLTExLjM1MikiIGFyaWEtbGFiZWw9
IjAiPgogICAgIDxwYXRoIGQ9Im0tNTEuNDcxIDI3Ni4xN2MxLjExNzYgMCAxLjgyODgtMC45OTkwNyAxLjgyODgtMi44MTk0IDAt
MS44MTE5LTAuNzExMi0yLjc2ODYtMS44Mjg4LTIuNzY4Ni0xLjExNzYgMC0xLjgyODggMC45NDgyNi0xLjgyODggMi43Njg2IDAg
MS44MjAzIDAuNzExMiAyLjgxOTQgMS44Mjg4IDIuODE5NHptMC0wLjc2MmMtMC41MTY0NyAwLTAuODk3NDctMC41MzM0LTAuODk3
NDctMi4wNTc0czAuMzgxLTIuMDA2NiAwLjg5NzQ3LTIuMDA2NmMwLjUyNDkzIDAgMC44OTc0NyAwLjQ4MjYgMC44OTc0NyAyLjAw
NjZzLTAuMzcyNTMgMi4wNTc0LTAuODk3NDcgMi4wNTc0eiIgZmlsbC1vcGFjaXR5PSIuMjUwOTgiIHN0cm9rZT0ibm9uZSIvPgog
ICAgPC9nPgogICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoMjIuNTA2KSIgYXJpYS1sYWJlbD0iNyI+CiAgICAgPHBhdGggZD0ibTEx
OC4xNSAyNDMuMDhoMC45OTA2YzAuMDkzMS0yLjA5OTcgMC4zNDcxMy0zLjIwODkgMS42NDI1LTQuNzkyMXYtMC41OTI2NmgtMy42
MTUzdjAuODIxMjZoMi41NTY5Yy0xLjA3NTMgMS40NjQ3LTEuNDczMiAyLjY1MDEtMS41NzQ4IDQuNTYzNXoiIGZpbGwtb3BhY2l0
eT0iLjEyNTQ5IiBzdHJva2U9Im5vbmUiLz4KICAgIDwvZz4KICAgIDxnIHRyYW5zZm9ybT0icm90YXRlKC05LjcyNzMpIiBhcmlh
LWxhYmVsPSIxIj4KICAgICA8cGF0aCBkPSJtLTE4LjI5OSAyODIuNzloMy4yNDI3di0wLjc5NTg3aC0xLjA1ODN2LTQuNTg4OWgt
MC43MjgxM2MtMC4zMzg2NyAwLjIwMzItMC43MTEyIDAuMzM4NjYtMS4yNDQ2IDAuNDQwMjZ2MC42MDk2aDAuOTkwNnYzLjUzOTFo
LTEuMjAyM3oiIGZpbGwtb3BhY2l0eT0iLjA2Mjc0NSIgc3Ryb2tlPSJub25lIi8+CiAgICA8L2c+CiAgIDwvZz4KICAgPGcgYXJp
YS1sYWJlbD0iLiI+CiAgICA8cGF0aCBkPSJtMjAuOTIgMjgzLjk4YzAuNjU0NzYgMCAxLjEyODktMC41MTkyOSAxLjEyODktMS4x
NzQgMC0wLjY1NDc2LTAuNDc0MTMtMS4xNzQtMS4xMjg5LTEuMTc0LTAuNjU0NzYgMC0xLjEyODkgMC41MTkyOS0xLjEyODkgMS4x
NzQgMCAwLjY1NDc1IDAuNDc0MTMgMS4xNzQgMS4xMjg5IDEuMTc0eiIvPgogICA8L2c+CiAgPC9nPgogPC9nPgo8L3N2Zz4K
")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]
#![cfg_attr(unsafe_in_unsafe, warn(unsafe_op_in_unsafe_fn))]
#![cfg_attr(not(unsafe_in_unsafe), allow(unused_unsafe))]
#![allow(
    clippy::missing_safety_doc,
    clippy::unnecessary_cast,
    clippy::useless_conversion
)]

pub mod gmp;
#[cfg(feature = "mpc")]
pub mod mpc;
#[cfg(feature = "mpfr")]
pub mod mpfr;

#[cfg(extended_key_value_attributes)]
pub mod C;

#[cfg(test)]
mod tests {
    use core::{slice, str};
    use libc::c_char;

    pub unsafe fn str_from_cstr<'a>(cstr: *const c_char) -> &'a str {
        let s = unsafe { slice::from_raw_parts(cstr as *const u8, libc::strlen(cstr)) };
        str::from_utf8(s).expect("version not utf8")
    }
}
