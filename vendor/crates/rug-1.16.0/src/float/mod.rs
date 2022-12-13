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
Multi-precision floating-point numbers with correct rounding.

This module provides support for floating-point numbers of type
[`Float`][crate::Float].
*/

pub(crate) mod arith;
pub(crate) mod big;
mod casts;
mod cmp;
#[cfg(feature = "num-traits")]
mod impl_num_traits;
mod ord;
#[cfg(feature = "serde")]
mod serde;
pub(crate) mod small;
#[cfg(test)]
pub(crate) mod tests;
mod traits;

pub use crate::float::{
    big::{BorrowFloat, ParseFloatError},
    ord::OrdFloat,
    small::{SmallFloat, ToSmall},
};
use az::SaturatingCast;
use core::{i32, u32};
use gmp_mpfr_sys::mpfr::{self, prec_t};

/**
Returns the minimum value for the exponent.

# Examples

```rust
use rug::float;
println!("Minimum exponent is {}", float::exp_min());
```
*/
#[inline]
pub fn exp_min() -> i32 {
    unsafe { mpfr::get_emin() }.saturating_cast()
}

/**
Returns the maximum value for the exponent.

# Examples

```rust
use rug::float;
println!("Maximum exponent is {}", float::exp_max());
```
*/
#[inline]
pub fn exp_max() -> i32 {
    unsafe { mpfr::get_emax() }.saturating_cast()
}

/**
Returns the maximum allowed range for the exponent.

# Examples

```rust
use rug::float;
let (min, max) = float::allowed_exp_range();
println!("Minimum and maximum exponents are in [{}, {}]", min, max);
```
*/
#[inline]
pub fn allowed_exp_range() -> (i32, i32) {
    unsafe {
        (
            mpfr::get_emin_min().saturating_cast(),
            mpfr::get_emax_max().saturating_cast(),
        )
    }
}

/**
Returns the minimum value for the precision.

# Examples

```rust
use rug::float;
println!("Minimum precision is {}", float::prec_min());
```
*/
#[inline]
pub const fn prec_min() -> u32 {
    mpfr::PREC_MIN as u32
}

/**
Returns the maximum value for the precision.

# Examples

```rust
use rug::float;
println!("Maximum precision is {}", float::prec_max());
```
*/
#[inline]
pub const fn prec_max() -> u32 {
    const MAX_FITS: bool = mpfr::PREC_MAX < u32::MAX as prec_t;
    const VALUES: [u32; 2] = [u32::MAX, mpfr::PREC_MAX as u32];
    const PREC_MAX: u32 = VALUES[MAX_FITS as usize];
    PREC_MAX
}

/**
The rounding methods for floating-point values.

When rounding to the nearest, if the number to be rounded is exactly between two
representable numbers, it is rounded to the even one, that is, the one with the
least significant bit set to zero.

# Examples

```rust
use rug::{float::Round, ops::AssignRound, Float};
let mut f4 = Float::new(4);
f4.assign_round(10.4, Round::Nearest);
assert_eq!(f4, 10);
f4.assign_round(10.6, Round::Nearest);
assert_eq!(f4, 11);
f4.assign_round(-10.7, Round::Zero);
assert_eq!(f4, -10);
f4.assign_round(10.3, Round::Up);
assert_eq!(f4, 11);
```

Rounding to the nearest will round numbers exactly between two representable
numbers to the even one.

```rust
use rug::{float::Round, ops::AssignRound, Float};
// 24 is 11000 in binary
// 25 is 11001 in binary
// 26 is 11010 in binary
// 27 is 11011 in binary
// 28 is 11100 in binary
let mut f4 = Float::new(4);
f4.assign_round(25, Round::Nearest);
assert_eq!(f4, 24);
f4.assign_round(27, Round::Nearest);
assert_eq!(f4, 28);
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
// TODO: replace with exhaustive once rustc dependency >= 1.40
#[allow(clippy::manual_non_exhaustive)]
pub enum Round {
    /// Round towards the nearest, with ties rounding to even.
    Nearest,
    /// Round towards zero.
    Zero,
    /// Round towards plus infinity.
    Up,
    /// Round towards minus infinity.
    Down,
    #[doc(hidden)]
    __Nonexhaustive,
}

impl Round {
    #[inline]
    /// Reverses the rounding direction.
    ///
    ///   * [`Up`] becomes [`Down`].
    ///   * [`Down`] becomes [`Up`].
    ///   * Other variants are not affected.
    ///
    /// [`Up`]: Round::Up
    /// [`Down`]: Round::Down
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::Round;
    ///
    /// assert_eq!(Round::Up.reverse(), Round::Down);
    /// assert_eq!(Round::Down.reverse(), Round::Up);
    /// assert_eq!(Round::Nearest.reverse(), Round::Nearest);
    /// ```
    #[must_use]
    pub fn reverse(self) -> Round {
        match self {
            Round::Up => Round::Down,
            Round::Down => Round::Up,
            _ => self,
        }
    }
}

impl Default for Round {
    #[inline]
    fn default() -> Round {
        Round::Nearest
    }
}

/**
The available floating-point constants.

# Examples

```rust
use rug::{float::Constant, Float};

let log2 = Float::with_val(53, Constant::Log2);
let pi = Float::with_val(53, Constant::Pi);
let euler = Float::with_val(53, Constant::Euler);
let catalan = Float::with_val(53, Constant::Catalan);

assert_eq!(log2.to_string_radix(10, Some(5)), "6.9315e-1");
assert_eq!(pi.to_string_radix(10, Some(5)), "3.1416");
assert_eq!(euler.to_string_radix(10, Some(5)), "5.7722e-1");
assert_eq!(catalan.to_string_radix(10, Some(5)), "9.1597e-1");
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
// TODO: replace with exhaustive once rustc dependency >= 1.40
#[allow(clippy::manual_non_exhaustive)]
pub enum Constant {
    /// The logarithm of two, 0.693147…
    Log2,
    /// The value of pi, π = 3.14159…
    Pi,
    /// Euler’s constant, also known as the Euler-Mascheroni constant, γ = 0.577215…
    ///
    /// Note that this is *not* Euler’s number e, which can be obtained using
    /// one of the [`exp`][crate::Float::exp] functions.
    Euler,
    /// Catalan’s constant, 0.915965…
    Catalan,
    #[doc(hidden)]
    __Nonexhaustive,
}

/**
Special floating-point values.

# Examples

```rust
use rug::{float::Special, Float};

let zero = Float::with_val(53, Special::Zero);
let neg_zero = Float::with_val(53, Special::NegZero);
let infinity = Float::with_val(53, Special::Infinity);
let neg_infinity = Float::with_val(53, Special::NegInfinity);
let nan = Float::with_val(53, Special::Nan);

assert_eq!(zero, 0);
assert!(zero.is_sign_positive());
assert_eq!(neg_zero, 0);
assert!(neg_zero.is_sign_negative());
assert!(infinity.is_infinite());
assert!(infinity.is_sign_positive());
assert!(neg_infinity.is_infinite());
assert!(neg_infinity.is_sign_negative());
assert!(nan.is_nan());
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
// TODO: replace with exhaustive once rustc dependency >= 1.40
#[allow(clippy::manual_non_exhaustive)]
pub enum Special {
    /// Positive zero.
    Zero,
    /// Negative zero.
    NegZero,
    /// Positive infinity.
    Infinity,
    /// Negative infinity.
    NegInfinity,
    /// Not a number.
    Nan,
    #[doc(hidden)]
    __Nonexhaustive,
}

/**
Specifies which cache to free.

# Examples

```rust
use rug::float::{self, FreeCache};
use std::thread;

fn main() {
    let child = thread::spawn(move || {
        // some work here that uses Float
        float::free_cache(FreeCache::Local);
    });
    // some work here
    child.join().expect("couldn't join thread");
    float::free_cache(FreeCache::All);
}
```
*/
#[allow(clippy::needless_doctest_main)]
// TODO: replace with exhaustive once rustc dependency >= 1.40
#[allow(clippy::manual_non_exhaustive)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FreeCache {
    /// Free caches local to the current thread.
    Local,
    /// Free caches shared by all threads.
    Global,
    /// Free both local and global caches.
    All,
    #[doc(hidden)]
    __Nonexhaustive,
}

/**
Frees various caches and memory pools that are used internally.

To avoid memory leaks being reported when using tools like [Valgrind], it is
advisable to free thread-local caches before terminating a thread and all caches
before exiting.

# Examples

```rust
use rug::float::{self, FreeCache};
use std::thread;

fn main() {
    let child = thread::spawn(move || {
        // some work here that uses Float
        float::free_cache(FreeCache::Local);
    });
    // some work here
    child.join().expect("couldn't join thread");
    float::free_cache(FreeCache::All);
}
```

[Valgrind]: https://www.valgrind.org/
*/
#[allow(clippy::needless_doctest_main)]
#[inline]
pub fn free_cache(which: FreeCache) {
    let way = match which {
        FreeCache::Local => mpfr::FREE_LOCAL_CACHE,
        FreeCache::Global => mpfr::FREE_GLOBAL_CACHE,
        FreeCache::All => mpfr::FREE_LOCAL_CACHE | mpfr::FREE_GLOBAL_CACHE,
        _ => unreachable!(),
    };
    unsafe {
        mpfr::free_cache2(way);
    }
}
