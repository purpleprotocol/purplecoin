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

use crate::{
    ext::xmpz,
    integer::ParseIntegerError,
    ops::{DivRounding, RemRounding},
    Assign, Integer,
};
use az::{CheckedCast, UnwrappedCast};
use core::cmp::Ordering;
use num_integer::{ExtendedGcd, Integer as NumInteger, Roots};
use num_traits_crate::{
    cast::{FromPrimitive, ToPrimitive},
    identities::{One, Zero},
    ops::mul_add::{MulAdd, MulAddAssign},
    sign::Signed,
    Num,
};

impl Zero for Integer {
    #[inline]
    fn zero() -> Self {
        Integer::new()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.cmp0() == Ordering::Equal
    }

    #[inline]
    fn set_zero(&mut self) {
        xmpz::set_0(self);
    }
}

impl One for Integer {
    #[inline]
    fn one() -> Self {
        Integer::from(1u8)
    }

    #[inline]
    fn set_one(&mut self) {
        xmpz::set_1(self);
    }

    #[inline]
    fn is_one(&self) -> bool {
        xmpz::is_1(self)
    }
}

impl Num for Integer {
    type FromStrRadixErr = ParseIntegerError;

    #[inline]
    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntegerError> {
        Integer::from_str_radix(src, radix.unwrapped_cast())
    }
}

impl Signed for Integer {
    #[inline]
    fn abs(&self) -> Self {
        self.abs_ref().into()
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        if *self <= *other {
            Integer::new()
        } else {
            (self - other).into()
        }
    }

    #[inline]
    fn signum(&self) -> Self {
        self.signum_ref().into()
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.cmp0() == Ordering::Greater
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.cmp0() == Ordering::Less
    }
}

impl MulAdd for Integer {
    type Output = Integer;

    #[inline]
    fn mul_add(self, a: Integer, b: Integer) -> Integer {
        &self * &a + b
    }
}

impl MulAddAssign for Integer {
    #[inline]
    fn mul_add_assign(&mut self, a: Integer, b: Integer) {
        *self = &*self * &a + b
    }
}

impl MulAdd<&Integer, &Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn mul_add(self, a: &Integer, b: &Integer) -> Integer {
        self * a + b
    }
}

impl MulAddAssign<&Integer, &Integer> for Integer {
    #[inline]
    fn mul_add_assign(&mut self, a: &Integer, b: &Integer) {
        *self *= a;
        *self += b;
    }
}

impl ToPrimitive for Integer {
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        self.checked_cast()
    }
    #[inline]
    fn to_u64(&self) -> Option<u64> {
        self.checked_cast()
    }
    #[inline]
    fn to_isize(&self) -> Option<isize> {
        self.checked_cast()
    }
    #[inline]
    fn to_i8(&self) -> Option<i8> {
        self.checked_cast()
    }
    #[inline]
    fn to_i16(&self) -> Option<i16> {
        self.checked_cast()
    }
    #[inline]
    fn to_i32(&self) -> Option<i32> {
        self.checked_cast()
    }
    #[inline]
    fn to_i128(&self) -> Option<i128> {
        self.checked_cast()
    }
    #[inline]
    fn to_usize(&self) -> Option<usize> {
        self.checked_cast()
    }
    #[inline]
    fn to_u8(&self) -> Option<u8> {
        self.checked_cast()
    }
    #[inline]
    fn to_u16(&self) -> Option<u16> {
        self.checked_cast()
    }
    #[inline]
    fn to_u32(&self) -> Option<u32> {
        self.checked_cast()
    }
    #[inline]
    fn to_u128(&self) -> Option<u128> {
        self.checked_cast()
    }
    #[inline]
    fn to_f32(&self) -> Option<f32> {
        Some(self.to_f32())
    }
    #[inline]
    fn to_f64(&self) -> Option<f64> {
        Some(self.to_f64())
    }
}

impl FromPrimitive for Integer {
    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_isize(n: isize) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i8(n: i8) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i16(n: i16) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i32(n: i32) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i128(n: i128) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_usize(n: usize) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u8(n: u8) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u16(n: u16) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u32(n: u32) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u128(n: u128) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        Self::from_f32(n)
    }
    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        Self::from_f64(n)
    }
}

impl NumInteger for Integer {
    #[inline]
    fn div_floor(&self, other: &Self) -> Self {
        DivRounding::div_floor(self, other).into()
    }
    #[inline]
    fn mod_floor(&self, other: &Self) -> Self {
        RemRounding::rem_floor(self, other).into()
    }
    #[inline]
    fn gcd(&self, other: &Self) -> Self {
        self.gcd_ref(other).into()
    }
    #[inline]
    fn lcm(&self, other: &Self) -> Self {
        self.lcm_ref(other).into()
    }
    #[inline]
    fn divides(&self, other: &Self) -> bool {
        other.is_divisible(self)
    }
    #[inline]
    fn is_multiple_of(&self, other: &Self) -> bool {
        other.is_divisible(self)
    }
    #[inline]
    fn is_even(&self) -> bool {
        self.is_even()
    }
    #[inline]
    fn is_odd(&self) -> bool {
        self.is_odd()
    }
    #[inline]
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        self.div_rem_ref(other).into()
    }

    #[inline]
    fn div_ceil(&self, other: &Self) -> Self {
        DivRounding::div_ceil(self, other).into()
    }
    #[inline]
    fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
        let gcd = Integer::from(self.gcd_ref(other));
        let lcm = if gcd.cmp0() == Ordering::Equal || other.cmp0() == Ordering::Equal {
            Integer::new()
        } else {
            Integer::from(self.div_exact_ref(&gcd)) * other
        };
        (gcd, lcm)
    }
    #[inline]
    fn extended_gcd(&self, other: &Self) -> ExtendedGcd<Self> {
        let mut gcdc = extended_gcd_hack::new();
        (&mut gcdc.gcd, &mut gcdc.x, &mut gcdc.y).assign(self.gcd_cofactors_ref(other));
        gcdc
    }
    #[inline]
    fn extended_gcd_lcm(&self, other: &Self) -> (ExtendedGcd<Self>, Self) {
        let gcdc = NumInteger::extended_gcd(self, other);
        let lcm = if gcdc.gcd.cmp0() == Ordering::Equal || other.cmp0() == Ordering::Equal {
            Integer::new()
        } else {
            Integer::from(self.div_exact_ref(&gcdc.gcd)) * other
        };
        (gcdc, lcm)
    }
    #[inline]
    fn div_mod_floor(&self, other: &Self) -> (Self, Self) {
        self.div_rem_floor_ref(other).into()
    }
    #[inline]
    fn next_multiple_of(&self, other: &Self) -> Self {
        let mut i = Integer::from(RemRounding::rem_floor(self, other));
        if i.cmp0() == Ordering::Equal {
            i.assign(self);
            i
        } else {
            other - i + self
        }
    }
    #[inline]
    fn prev_multiple_of(&self, other: &Self) -> Self {
        let mut i = Integer::from(RemRounding::rem_floor(self, other));
        if i.cmp0() == Ordering::Equal {
            i.assign(self);
            i
        } else {
            self - i
        }
    }
}

impl Roots for Integer {
    #[inline]
    fn nth_root(&self, n: u32) -> Self {
        self.root_ref(n).into()
    }

    #[inline]
    fn sqrt(&self) -> Self {
        self.sqrt_ref().into()
    }

    #[inline]
    fn cbrt(&self) -> Self {
        self.root_ref(3).into()
    }
}

// Ugh, ExtendedGcd has no public constructor and a hidden field, so we have to
// use this ugly ugly hack to create it.
mod extended_gcd_hack {
    use super::*;
    use core::{
        mem,
        ops::{Add, Div, Mul, Rem, Sub},
    };

    pub fn new() -> ExtendedGcd<Integer> {
        let zero = <IntegerHack as Zero>::zero();
        let extended = <IntegerHack as NumInteger>::extended_gcd(&zero, &zero);
        // SAFETY: IntegerHack is ABI-compatible with Integer, so we can transmute
        unsafe { mem::transmute(extended) }
    }

    #[repr(transparent)]
    #[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
    struct IntegerHack(Integer);

    impl Add for IntegerHack {
        type Output = Self;
        fn add(self, rhs: Self) -> Self {
            IntegerHack(<Integer as Add>::add(self.0, rhs.0))
        }
    }
    impl Sub for IntegerHack {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self {
            IntegerHack(<Integer as Sub>::sub(self.0, rhs.0))
        }
    }
    impl Mul for IntegerHack {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self {
            IntegerHack(<Integer as Mul>::mul(self.0, rhs.0))
        }
    }
    impl Div for IntegerHack {
        type Output = Self;
        fn div(self, rhs: Self) -> Self {
            IntegerHack(<Integer as Div>::div(self.0, rhs.0))
        }
    }
    impl Rem for IntegerHack {
        type Output = Self;
        fn rem(self, rhs: Self) -> Self {
            IntegerHack(<Integer as Rem>::rem(self.0, rhs.0))
        }
    }
    impl Zero for IntegerHack {
        #[inline]
        fn zero() -> Self {
            IntegerHack(<Integer as Zero>::zero())
        }
        #[inline]
        fn is_zero(&self) -> bool {
            <Integer as Zero>::is_zero(&self.0)
        }
    }
    impl One for IntegerHack {
        #[inline]
        fn one() -> Self {
            IntegerHack(<Integer as One>::one())
        }
    }
    impl Num for IntegerHack {
        type FromStrRadixErr = <Integer as Num>::FromStrRadixErr;
        #[inline]
        fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
            <Integer as Num>::from_str_radix(str, radix).map(IntegerHack)
        }
    }
    impl NumInteger for IntegerHack {
        #[inline]
        fn div_floor(&self, other: &Self) -> Self {
            IntegerHack(<Integer as NumInteger>::div_floor(&self.0, &other.0))
        }
        #[inline]
        fn mod_floor(&self, other: &Self) -> Self {
            IntegerHack(<Integer as NumInteger>::mod_floor(&self.0, &other.0))
        }
        #[inline]
        fn gcd(&self, other: &Self) -> Self {
            IntegerHack(<Integer as NumInteger>::gcd(&self.0, &other.0))
        }
        #[inline]
        fn lcm(&self, other: &Self) -> Self {
            IntegerHack(<Integer as NumInteger>::lcm(&self.0, &other.0))
        }
        #[inline]
        fn divides(&self, other: &Self) -> bool {
            <Integer as NumInteger>::divides(&self.0, &other.0)
        }
        #[inline]
        fn is_multiple_of(&self, other: &Self) -> bool {
            <Integer as NumInteger>::is_multiple_of(&self.0, &other.0)
        }
        #[inline]
        fn is_even(&self) -> bool {
            <Integer as NumInteger>::is_even(&self.0)
        }
        #[inline]
        fn is_odd(&self) -> bool {
            <Integer as NumInteger>::is_odd(&self.0)
        }
        #[inline]
        fn div_rem(&self, other: &Self) -> (Self, Self) {
            let (div, rem) = <Integer as NumInteger>::div_rem(&self.0, &other.0);
            (IntegerHack(div), IntegerHack(rem))
        }
    }
}
