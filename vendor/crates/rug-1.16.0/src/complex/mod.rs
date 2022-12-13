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
Multi-precision complex numbers with correct rounding.

This module provides support for complex numbers of type
[`Complex`][crate::Complex].
*/

pub(crate) mod arith;
pub(crate) mod big;
mod cmp;
#[cfg(feature = "num-traits")]
mod impl_num_traits;
mod ord;
#[cfg(feature = "serde")]
mod serde;
mod small;
#[cfg(test)]
mod tests;
mod traits;

pub use crate::complex::big::{BorrowComplex, ParseComplexError};
pub use crate::complex::ord::OrdComplex;
pub use crate::complex::small::SmallComplex;

/**
The `Prec` trait is used to specify the precision of the real and imaginary
parts of a [`Complex`][crate::Complex] number.

This trait is implememented for [`u32`] and for <code>[(][tuple][u32][], [u32][][)][tuple]</code>.

# Examples

```rust
use rug::Complex;
let c1 = Complex::new(32);
assert_eq!(c1.prec(), (32, 32));
let c2 = Complex::new((32, 64));
assert_eq!(c2.prec(), (32, 64));
```

[`Complex`]: `crate::Complex`
*/
pub trait Prec {
    /// Returns the precision for the real and imaginary parts.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::complex::Prec;
    /// assert_eq!(Prec::prec(24), (24, 24));
    /// assert_eq!(Prec::prec((24, 53)), (24, 53));
    /// ```
    fn prec(self) -> (u32, u32);
}

impl Prec for u32 {
    #[inline]
    fn prec(self) -> (u32, u32) {
        (self, self)
    }
}

impl Prec for (u32, u32) {
    #[inline]
    fn prec(self) -> (u32, u32) {
        self
    }
}
