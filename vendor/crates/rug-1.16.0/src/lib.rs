// Copyright © 2016–2022 Trevor Spiteri

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU Lesser General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU Lesser General Public License and
// a copy of the GNU General Public License along with this program. If not, see
// <https://www.gnu.org/licenses/>.

/*!
# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary precision and
correct rounding:

  * [`Integer`] is a bignum integer with arbitrary precision,
  * [`Rational`] is a bignum rational number with arbitrary precision,
  * [`Float`] is a multi-precision floating-point number with correct rounding,
    and
  * [`Complex`] is a multi-precision complex number with correct rounding.

Rug is a high-level interface to the following [GNU] libraries:

  * [GMP] for integers and rational numbers,
  * [MPFR] for floating-point numbers, and
  * [MPC] for complex numbers.

Rug is free software: you can redistribute it and/or modify it under the terms
of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version. See the full text of the [GNU LGPL] and [GNU GPL] for details.

You are also free to use the examples in this documentation without any
restrictions; the examples are in the public domain.

## Quick example

```rust
# #[cfg(feature = "integer")] {
use rug::{Assign, Integer};
let mut int = Integer::new();
assert_eq!(int, 0);
int.assign(14);
assert_eq!(int, 14);

let decimal = "98_765_432_109_876_543_210";
int.assign(Integer::parse(decimal).unwrap());
assert!(int > 100_000_000);

let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
int.assign(Integer::parse_radix(hex_160, 16).unwrap());
assert_eq!(int.significant_bits(), 160);
int = (int >> 128) - 1;
assert_eq!(int, 0xfffe_ffff_u32);
# }
```

  * <code>[Integer]::[new][Integer::new]</code> creates a new [`Integer`]
    intialized to zero.
  * To assign values to Rug types, we use the [`Assign`] trait and its method
    [`Assign::assign`]. We do not use the [assignment operator `=`][assignment]
    as that would drop the left-hand-side operand and replace it with a
    right-hand-side operand of the same type, which is not what we want here.
  * Arbitrary precision numbers can hold numbers that are too large to fit in a
    primitive type. To assign such a number to the large types, we use strings
    rather than primitives; in the example this is done using
    <code>[Integer]::[parse][Integer::parse]</code> and
    <code>[Integer]::[parse\_radix][Integer::parse_radix]</code>.
  * We can compare Rug types to primitive types or to other Rug types using the
    normal comparison operators, for example `int > 100_000_000`.
  * Most arithmetic operations are supported with Rug types and primitive types
    on either side of the operator, for example `int >> 128`.

## Using with primitive types

With Rust primitive types, arithmetic operators usually operate on two values of
the same type, for example `12i32 + 5i32`. Unlike primitive types, conversion to
and from Rug types can be expensive, so the arithmetic operators are overloaded
to work on many combinations of Rug types and primitives. The following are
provided:

 1. Where they make sense, all arithmetic operators are overloaded to work with
    Rug types and the primitives [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], [`f32`] and [`f64`].
 2. Where they make sense, conversions using the [`From`] trait and assignments
    using the [`Assign`] trait are supported for all the primitives in 1 above
    as well as [`bool`], [`isize`] and [`usize`].
 3. Comparisons between Rug types and all the numeric primitives listed in 1 and
    2 above are supported.
 4. For [`Rational`] numbers, conversions and comparisons are also supported for
    tuples containing two integer primitives: the first is the numerator and the
    second is the denominator which must not be zero. The two primitives do not
    need to be of the same type.
 5. For [`Complex`] numbers, conversions and comparisons are also supported for
    tuples containing two primitives: the first is the real part and the second
    is the imaginary part. The two primitives do not need to be of the same
    type.

## Operators

Operators are overloaded to work on Rug types alone or on a combination of Rug
types and Rust primitives. When at least one operand is an owned value of a Rug
type, the operation will consume that value and return a value of the Rug type.
For example

```rust
# #[cfg(feature = "integer")] {
use rug::Integer;
let a = Integer::from(10);
let b = 5 - a;
assert_eq!(b, 5 - 10);
# }
```

Here `a` is consumed by the subtraction, and `b` is an owned [`Integer`].

If on the other hand there are no owned Rug types and there are references
instead, the returned value is not the final value, but an
incomplete-computation value. For example

```rust
# #[cfg(feature = "integer")] {
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
// This would fail to compile: assert_eq!(incomplete, -10);
let sub = Integer::from(incomplete);
assert_eq!(sub, -10);
# }
```

Here `a` and `b` are not consumed, and `incomplete` is not the final value. It
still needs to be converted or assigned into an [`Integer`]. This is covered in
more detail in the [*Incomplete-computation values*] section.

### Shifting operations

The left shift `<<` and right shift `>>` operators support shifting by negative
values, for example `a << 5` is equivalent to `a >> -5`.

The shifting operators are also supported for the [`Float`] and [`Complex`]
number types, where they are equivalent to multiplication or division by a power
of two. Only the exponent of the value is affected; the mantissa is unchanged.

### Exponentiation

Exponentiation (raising to a power) does not have a dedicated operator in Rust.
In order to perform exponentiation of Rug types, the [`Pow`][ops::Pow] trait has
to be brought into scope, for example

```rust
# #[cfg(feature = "integer")] {
use rug::{ops::Pow, Integer};
let base = Integer::from(10);
let power = base.pow(5);
assert_eq!(power, 100_000);
# }
```

### Compound assignments to right-hand-side operands

Traits are provided for compound assignment to right-hand-side operands. This
can be useful for non-commutative operations like subtraction. The names of the
traits and their methods are similar to Rust compound assignment traits, with
the suffix “`Assign`” replaced with “`From`”. For example the counterpart to
[`SubAssign`][core::ops::SubAssign] is [`SubFrom`][ops::SubFrom]:

```rust
# #[cfg(feature = "integer")] {
use rug::{ops::SubFrom, Integer};
let mut rhs = Integer::from(10);
// set rhs = 100 - rhs
rhs.sub_from(100);
assert_eq!(rhs, 90);
# }
```

## Incomplete-computation values

There are two main reasons why operations like `&a - &b` do not perform a
complete computation and return a Rug type:

 1. Sometimes we need to assign the result to an object that already exists.
    Since Rug types require memory allocations, this can help reduce the number
    of allocations. (While the allocations might not affect performance
    noticeably for computationally intensive functions, they can have a much
    more significant effect on faster functions like addition.)
 2. For the [`Float`] and [`Complex`] number types, we need to know the
    precision when we create a value, and the operation itself does not convey
    information about what precision is desired for the result.

There are two things that can be done with incomplete-computation values:

 1. Assign them to an existing object without unnecessary allocations. This is
    usually achieved using the [`Assign`] trait or a similar method, for example
    <code>int.[assign][Assign::assign]\(incomplete)</code> and
    <code>float.[assign\_round][ops::AssignRound::assign_round]\(incomplete, [Round][float::Round]::[Up][float::Round::Up])</code>.
 2. Convert them to the final value using the [`Complete`] trait, the [`From`]
    trait or a similar method. For example incomplete integers can be completed
    using <code>incomplete.[complete][Complete::complete]\()</code> or
    <code>[Integer]::[from][From::from]\(incomplete)</code>. Incomplete
    floating-point numbers can be completed using
    <code>[Float]::[with_val][Float::with_val]\(53, incomplete)</code> since the
    precision has to be specified.

Let us consider a couple of examples.

```rust
# #[cfg(feature = "integer")] {
use rug::{Assign, Integer};
let mut buffer = Integer::new();
// ... buffer can be used and reused ...
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
buffer.assign(incomplete);
assert_eq!(buffer, -10);
# }
```

Here the assignment from `incomplete` into `buffer` does not require an
allocation unless the result does not fit in the current capacity of `buffer`.
If `&a - &b` returned an [`Integer`] instead, then an allocation would take
place even if it is not necessary.

```rust
# #[cfg(feature = "float")] {
use rug::{float::Constant, Float};
// x has a precision of 10 bits
let x = Float::with_val(10, 180);
// y has a precision of 50 bits
let y = Float::with_val(50, Constant::Pi);
let incomplete = &x / &y;
// z has a precision of 45 bits
let z = Float::with_val(45, incomplete);
assert!(57.295 < z && z < 57.296);
# }
```

The precision to use for the result depends on the requirements of the algorithm
being implemented. Here `z` is created with a precision of 45.

Many operations can return incomplete-computation values, for example

  * unary operators applied to references, for example `-&int`
  * binary operators applied to two references, for example `&int1 + &int2`
  * binary operators applied to a primitive and a reference, for example `&int *
    10`
  * methods that take a reference, for example
    <code>int.[abs\_ref][Integer::abs_ref]\()</code>
  * methods that take two references, for example
    <code>int1.[gcd\_ref][Integer::gcd_ref]\(\&int2)</code>
  * string parsing, for example
    <code>[Integer]::[parse][Integer::parse]\(\"12\")</code>

These operations return objects that can be stored in temporary variables like
`incomplete` in the last few code examples. However, the names of the types are
not public, and consequently, the incomplete-computation values cannot be for
example stored in a struct. If you need to store the value in a struct, complete
it to its final type and value.

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate, add it as
a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
rug = "1.16"
```

Rug requires rustc version 1.37.0 or later.

Rug also depends on the [GMP], [MPFR] and [MPC] libraries through the low-level
FFI bindings in the [gmp-mpfr-sys crate][sys crate], which needs some setup to
build; the [gmp-mpfr-sys documentation][sys] has some details on usage under
[GNU/Linux][sys gnu], [macOS][sys mac] and [Windows][sys win].

## Optional features

The Rug crate has six optional features:

 1. `integer`, enabled by default. Required for the [`Integer`] type and its
    supporting features.
 2. `rational`, enabled by default. Required for the [`Rational`] number type
    and its supporting features. This feature requires the `integer` feature.
 3. `float`, enabled by default. Required for the [`Float`] type and its
    supporting features.
 4. `complex`, enabled by default. Required for the [`Complex`] number type and
    its supporting features. This feature requires the `float` feature.
 5. `rand`, enabled by default. Required for the [`RandState`][rand::RandState]
    type and its supporting features. This feature requires the `integer`
    feature.
 6. `serde`, disabled by default. This provides serialization support for the
    [`Integer`], [`Rational`], [`Float`] and [`Complex`] number types, providing
    that they are enabled. This feature requires the [serde crate].

The first five optional features are enabled by default; to use features
selectively, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.rug]
version = "1.16"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If none of the
features are selected, the [gmp-mpfr-sys crate][sys crate] is not required and
thus not enabled. In that case, only the [`Assign`] trait and the traits that
are in the [`ops`] module are provided by the crate.

## Experimental optional features

It is not considered a breaking change if the following experimental features
are removed. The removal of experimental features would however require a minor
version bump. Similarly, on a minor version bump, optional dependencies can be
updated to an incompatible newer version.

 1. `num-traits`, disabled by default. This implements some traits from the
    [*num-traits* crate] and the [*num-integer* crate].

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: #incomplete-computation-values
[*num-integer* crate]: https://crates.io/crates/num-integer
[*num-traits* crate]: https://crates.io/crates/num-traits
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: gmp_mpfr_sys#building-on-gnulinux
[sys mac]: gmp_mpfr_sys#building-on-macos
[sys win]: gmp_mpfr_sys#building-on-windows
[sys]: gmp_mpfr_sys
*/
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/rug/~1.16")]
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
// allowed to deal with e.g. 1i32.into(): c_long which can be i32 or i64
#![allow(clippy::useless_conversion)]
// matches! requires rustc 1.42
#![allow(clippy::match_like_matches_macro)]
#[macro_use]
mod macros;
mod ext;
#[cfg(any(feature = "integer", feature = "float"))]
mod misc;
mod ops_prim;
#[cfg(all(feature = "serde", any(feature = "integer", feature = "float")))]
mod serdeize;

pub mod ops;

/**
Assigns to a number from another value.

# Examples

Implementing the trait:

```rust
use rug::Assign;
struct I(i32);
impl Assign<i16> for I {
    fn assign(&mut self, rhs: i16) {
        self.0 = rhs.into();
    }
}
let mut i = I(0);
i.assign(42_i16);
assert_eq!(i.0, 42);
```

Performing an assignment operation using the trait:

```rust
# #[cfg(feature = "integer")] {
use rug::{Assign, Integer};
let mut i = Integer::from(15);
assert_eq!(i, 15);
i.assign(23);
assert_eq!(i, 23);
# }
```
*/
pub trait Assign<Src = Self> {
    /// Peforms the assignement.
    fn assign(&mut self, src: Src);
}

/**
Completes an [incomplete-computation value][icv].

# Examples

Implementing the trait:

```rust
# #[cfg(feature = "integer")] {
use rug::{Complete, Integer};
struct LazyPow4<'a>(&'a Integer);
impl Complete for LazyPow4<'_> {
    type Completed = Integer;
    fn complete(self) -> Integer {
        self.0.clone().square().square()
    }
}

assert_eq!(LazyPow4(&Integer::from(3)).complete(), 3i32.pow(4));
# }
```

Completing an [incomplete-computation value][icv]:

```rust
# #[cfg(feature = "integer")] {
use rug::{Complete, Integer};
let incomplete = Integer::fibonacci(12);
let complete = incomplete.complete();
assert_eq!(complete, 144);
# }
```

[icv]: crate#incomplete-computation-values
*/
pub trait Complete {
    /// The type of the completed operation.
    type Completed;

    /// Completes the operation.
    fn complete(self) -> Self::Completed;

    /// Completes the operation and stores the result in a target.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::{Complete, Integer};
    /// let mut complete = Integer::new();
    /// Integer::fibonacci(12).complete_into(&mut complete);
    /// assert_eq!(complete, 144);
    /// # }
    /// ```
    #[inline]
    fn complete_into<T>(self, target: &mut T)
    where
        Self: Sized,
        T: Assign<Self>,
    {
        target.assign(self);
    }
}

#[cfg(feature = "integer")]
pub mod integer;
#[cfg(feature = "integer")]
pub use crate::integer::big::Integer;

#[cfg(feature = "rational")]
pub mod rational;
#[cfg(feature = "rational")]
pub use crate::rational::big::Rational;

#[cfg(feature = "float")]
pub mod float;
#[cfg(feature = "float")]
pub use crate::float::big::Float;

#[cfg(feature = "complex")]
pub mod complex;
#[cfg(feature = "complex")]
pub use crate::complex::big::Complex;

#[cfg(feature = "rand")]
pub mod rand;

#[cfg(any(feature = "integer", feature = "float"))]
mod static_assertions {
    use core::mem;
    use gmp_mpfr_sys::gmp::{limb_t, LIMB_BITS, NAIL_BITS, NUMB_BITS};

    static_assert!(NAIL_BITS == 0);
    static_assert!(NUMB_BITS == LIMB_BITS);
    static_assert!(cfg!(target_pointer_width = "32") ^ cfg!(target_pointer_width = "64"));
    static_assert!(cfg!(gmp_limb_bits_32) ^ cfg!(gmp_limb_bits_64));
    #[cfg(gmp_limb_bits_64)]
    static_assert!(NUMB_BITS == 64);
    #[cfg(gmp_limb_bits_32)]
    static_assert!(NUMB_BITS == 32);
    static_assert!(NUMB_BITS % 8 == 0);
    static_assert!(mem::size_of::<limb_t>() == NUMB_BITS as usize / 8);
}

#[cfg(all(test, any(feature = "integer", feature = "float")))]
mod tests {
    #[cfg(any(feature = "rational", feature = "float"))]
    use core::{f32, f64};
    use core::{i128, i16, i32, i64, i8, isize, u128, u16, u32, u64, u8, usize};

    pub const U8: &[u8] = &[0, 1, 100, 101, i8::MAX as u8 + 1, u8::MAX];
    pub const I8: &[i8] = &[i8::MIN, -101, -100, -1, 0, 1, 100, 101, i8::MAX];
    pub const U16: &[u16] = &[0, 1, 1000, 1001, i16::MAX as u16 + 1, u16::MAX];
    pub const I16: &[i16] = &[i16::MIN, -1001, -1000, -1, 0, 1, 1000, 1001, i16::MAX];
    pub const U32: &[u32] = &[0, 1, 1000, 1001, i32::MAX as u32 + 1, u32::MAX];
    pub const I32: &[i32] = &[i32::MIN, -1001, -1000, -1, 0, 1, 1000, 1001, i32::MAX];
    pub const U64: &[u64] = &[
        0,
        1,
        1000,
        1001,
        i32::MAX as u64 + 1,
        u32::MAX as u64 + 1,
        u64::MAX,
    ];
    pub const I64: &[i64] = &[
        i64::MIN,
        -(u32::MAX as i64) - 1,
        i32::MIN as i64 - 1,
        -1001,
        -1000,
        -1,
        0,
        1,
        1000,
        1001,
        i32::MAX as i64 + 1,
        u32::MAX as i64 + 1,
        i64::MAX,
    ];
    pub const U128: &[u128] = &[
        0,
        1,
        1000,
        1001,
        i32::MAX as u128 + 1,
        u32::MAX as u128 + 1,
        i64::MAX as u128 + 1,
        u64::MAX as u128 + 1,
        u128::MAX,
    ];
    pub const I128: &[i128] = &[
        i128::MIN,
        -(u64::MAX as i128) - 1,
        i64::MIN as i128 - 1,
        -(u32::MAX as i128) - 1,
        i32::MIN as i128 - 1,
        -1001,
        -1000,
        -1,
        0,
        1,
        1000,
        1001,
        i32::MAX as i128 + 1,
        u32::MAX as i128 + 1,
        i64::MAX as i128 + 1,
        u64::MAX as i128 + 1,
        i128::MAX,
    ];
    pub const USIZE: &[usize] = &[0, 1, 1000, 1001, isize::MAX as usize + 1, usize::MAX];
    pub const ISIZE: &[isize] = &[isize::MIN, -1001, -1000, -1, 0, 1, 1000, 1001, isize::MAX];
    #[cfg(any(feature = "rational", feature = "float"))]
    pub const F32: &[f32] = &[
        -f32::NAN,
        f32::NEG_INFINITY,
        f32::MIN,
        -12.0e30,
        -2.0,
        -1.0 - f32::EPSILON,
        -1.0,
        -f32::MIN_POSITIVE,
        -f32::MIN_POSITIVE * f32::EPSILON,
        -0.0,
        0.0,
        f32::MIN_POSITIVE * f32::EPSILON,
        f32::MIN_POSITIVE,
        1.0,
        1.0 + f32::EPSILON,
        2.0,
        12.0e30,
        f32::MAX,
        f32::INFINITY,
        f32::NAN,
    ];
    #[cfg(any(feature = "rational", feature = "float"))]
    pub const F64: &[f64] = &[
        -f64::NAN,
        f64::NEG_INFINITY,
        f64::MIN,
        -12.0e43,
        -2.0,
        -1.0 - f64::EPSILON,
        -1.0,
        -f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE * f64::EPSILON,
        -0.0,
        0.0,
        f64::MIN_POSITIVE * f64::EPSILON,
        f64::MIN_POSITIVE,
        1.0,
        1.0 + f64::EPSILON,
        2.0,
        12.0e43,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
}
