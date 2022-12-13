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
    ext::xmpfr::{self, raw_round},
    float::{self, Round, Special},
    misc::NegAbs,
    Assign, Float,
};
use az::{Az, UnwrappedCast, WrappingCast};
use core::{
    cell::UnsafeCell,
    mem::{self, MaybeUninit},
    ops::Deref,
    ptr::NonNull,
};
use gmp_mpfr_sys::{
    gmp::{self, limb_t},
    mpfr::{self, exp_t, mpfr_t, prec_t},
};
use libc::c_int;

const LIMBS_IN_SMALL: usize = (128 / gmp::LIMB_BITS) as usize;
type Limbs = [MaybeUninit<limb_t>; LIMBS_IN_SMALL];

/**
A small float that does not require any memory allocation.

This can be useful when you have a primitive number type but need a reference to
a [`Float`]. The `SmallFloat` will have a precision according to the type of the
primitive used to set its value.

  * [`i8`], [`u8`]: the `SmallFloat` will have eight bits of precision.
  * [`i16`], [`u16`]: the `SmallFloat` will have 16 bits of precision.
  * [`i32`], [`u32`]: the `SmallFloat` will have 32 bits of precision.
  * [`i64`], [`u64`]: the `SmallFloat` will have 64 bits of precision.
  * [`i128`], [`u128`]: the `SmallFloat` will have 128 bits of precision.
  * [`isize`], [`usize`]: the `SmallFloat` will have 32 or 64 bits of precision,
    depending on the platform.
  * [`f32`]: the `SmallFloat` will have 24 bits of precision.
  * [`f64`]: the `SmallFloat` will have 53 bits of precision.
  * [`Special`]: the `SmallFloat` will have the [minimum possible
    precision][crate::float::prec_min].

The `SmallFloat` type can be coerced to a [`Float`], as it implements
<code>[Deref]\<[Target][Deref::Target] = [Float]></code>.

# Examples

```rust
use rug::{float::SmallFloat, Float};
// `a` requires a heap allocation, has 53-bit precision
let mut a = Float::with_val(53, 250);
// `b` can reside on the stack
let b = SmallFloat::from(-100f64);
a += &*b;
assert_eq!(a, 150);
// another computation:
a *= &*b;
assert_eq!(a, -15000);
```
*/
#[derive(Clone)]
pub struct SmallFloat {
    inner: Mpfr,
    limbs: Limbs,
}

// Safety: Mpfr has a repr equivalent to mpfr_t. The difference in the repr(C)
// types Mpfr and mpfr_t is that Mpfr uses UnsafeCell<NonNull<limb_t>> instead
// of NonNull<limb_t>, but UnsafeCell is repr(transparent).
#[repr(C)]
pub struct Mpfr {
    pub prec: prec_t,
    pub sign: c_int,
    pub exp: exp_t,
    pub d: UnsafeCell<NonNull<limb_t>>,
}

impl Clone for Mpfr {
    fn clone(&self) -> Mpfr {
        Mpfr {
            prec: self.prec,
            sign: self.sign,
            exp: self.exp,
            d: UnsafeCell::new(unsafe { *self.d.get() }),
        }
    }
}

static_assert!(mem::size_of::<Limbs>() == 16);
static_assert_same_layout!(Mpfr, mpfr_t);

// Safety: SmallFloat cannot be Sync because it contains an UnsafeCell
// which is written to then read without further protection, so it
// could lead to data races. But SmallFloat can be Send because if it
// is owned, no other reference can be used to modify the UnsafeCell.
unsafe impl Send for SmallFloat {}

impl Default for SmallFloat {
    #[inline]
    fn default() -> Self {
        SmallFloat::new()
    }
}

impl SmallFloat {
    /// Creates a [`SmallFloat`] with value 0 and the [minimum possible
    /// precision][crate::float::prec_min].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::SmallFloat;
    /// let f = SmallFloat::new();
    /// // Borrow f as if it were Float.
    /// assert_eq!(*f, 0);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        SmallFloat {
            inner: Mpfr {
                prec: float::prec_min() as prec_t,
                sign: 1,
                exp: xmpfr::EXP_ZERO,
                d: UnsafeCell::new(NonNull::dangling()),
            },
            limbs: small_limbs![],
        }
    }

    /// Returns a mutable reference to a [`Float`] for simple operations that do
    /// not need to change the precision of the number.
    ///
    /// # Safety
    ///
    /// It is undefined behavior modify the precision of the referenced
    /// [`Float`] or to swap it with another number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::SmallFloat;
    /// let mut f = SmallFloat::from(1.0f32);
    /// // addition does not change the precision
    /// unsafe {
    ///     *f.as_nonreallocating_float() += 2.0;
    /// }
    /// assert_eq!(*f, 3.0);
    /// ```
    #[inline]
    // Safety: after calling update_d(), self.inner.d points to the
    // limbs so it is in a consistent state.
    pub unsafe fn as_nonreallocating_float(&mut self) -> &mut Float {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Float);
        unsafe { &mut *ptr }
    }

    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limb won't move around, and we
        // can set the d field.
        let d = NonNull::<[MaybeUninit<limb_t>]>::from(&self.limbs[..]);
        // Safety: self is not Sync, so we can write to d without causing a data race.
        unsafe {
            *self.inner.d.get() = d.cast();
        }
    }
}

impl Deref for SmallFloat {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Float);
        // Safety: since we called update_d, the inner pointer is
        // pointing to the limbs and the number is in a consistent
        // state.
        unsafe { &*ptr }
    }
}

/// Types implementing this trait can be converted to [`SmallFloat`].
///
/// The following are implemented when `T` implements `ToSmall`:
///   * <code>[Assign]\<T> for [SmallFloat]</code>
///   * <code>[From]\<T> for [SmallFloat]</code>
///
/// This trait is sealed and cannot be implemented for more types; it is
/// implemented for the integer types [`i8`], [`i16`], [`i32`], [`i64`],
/// [`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`] and
/// [`usize`], and for the floating-point types [`f32`] and [`f64`].
pub trait ToSmall: SealedToSmall {}

pub trait SealedToSmall: Copy {
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs);
}

macro_rules! unsafe_signed {
    ($($I:ty)*) => { $(
        impl ToSmall for $I {}
        impl SealedToSmall for $I {
            #[inline]
            unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
                let (neg, abs) = self.neg_abs();
                unsafe{
                    abs.copy(inner, limbs);
                    if neg {
                        (*inner).sign = -1;
                    }
                }
            }
        }
    )* };
}

macro_rules! unsafe_unsigned_32 {
    ($U:ty, $bits:expr) => {
        impl ToSmall for $U {}
        impl SealedToSmall for $U {
            #[inline]
            unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
                let ptr = cast_ptr_mut!(inner, mpfr_t);
                let limbs_ptr = cast_ptr_mut!(limbs.as_mut_ptr(), limb_t);
                if self == 0 {
                    unsafe {
                        xmpfr::custom_zero(ptr, limbs_ptr, $bits);
                    }
                } else {
                    let leading = self.leading_zeros();
                    let limb_leading = leading + gmp::LIMB_BITS.az::<u32>() - $bits;
                    limbs[0] = MaybeUninit::new(limb_t::from(self) << limb_leading);
                    let exp = ($bits - leading).unwrapped_cast();
                    unsafe {
                        xmpfr::custom_regular(ptr, limbs_ptr, exp, $bits);
                    }
                }
            }
        }
    };
}

unsafe_signed! { i8 i16 i32 i64 i128 isize }

unsafe_unsigned_32! { u8, 8 }
unsafe_unsigned_32! { u16, 16 }
unsafe_unsigned_32! { u32, 32 }

impl ToSmall for u64 {}
impl SealedToSmall for u64 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = cast_ptr_mut!(limbs.as_mut_ptr(), limb_t);
        if self == 0 {
            unsafe {
                xmpfr::custom_zero(ptr, limbs_ptr, 64);
            }
        } else {
            let leading = self.leading_zeros();
            let sval = self << leading;
            #[cfg(gmp_limb_bits_64)]
            {
                limbs[0] = MaybeUninit::new(sval);
            }
            #[cfg(gmp_limb_bits_32)]
            {
                limbs[0] = MaybeUninit::new(sval.wrapping_cast());
                limbs[1] = MaybeUninit::new((sval >> 32).wrapping_cast());
            }
            let exp = (64 - leading).unwrapped_cast();
            unsafe {
                xmpfr::custom_regular(ptr, limbs_ptr, exp, 64);
            }
        }
    }
}

impl ToSmall for u128 {}
impl SealedToSmall for u128 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = cast_ptr_mut!(limbs.as_mut_ptr(), limb_t);
        if self == 0 {
            unsafe {
                xmpfr::custom_zero(ptr, limbs_ptr, 128);
            }
        } else {
            let leading = self.leading_zeros();
            let sval = self << leading;
            #[cfg(gmp_limb_bits_64)]
            {
                limbs[0] = MaybeUninit::new(sval.wrapping_cast());
                limbs[1] = MaybeUninit::new((sval >> 64).wrapping_cast());
            }
            #[cfg(gmp_limb_bits_32)]
            {
                limbs[0] = MaybeUninit::new(sval.wrapping_cast());
                limbs[1] = MaybeUninit::new((sval >> 32).wrapping_cast());
                limbs[2] = MaybeUninit::new((sval >> 64).wrapping_cast());
                limbs[3] = MaybeUninit::new((sval >> 96).wrapping_cast());
            }
            let exp = (128 - leading).unwrapped_cast();
            unsafe {
                xmpfr::custom_regular(ptr, limbs_ptr, exp, 128);
            }
        }
    }
}

impl ToSmall for usize {}
impl SealedToSmall for usize {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        #[cfg(target_pointer_width = "32")]
        {
            let val = self.az::<u32>();
            unsafe {
                val.copy(inner, limbs);
            }
        }
        #[cfg(target_pointer_width = "64")]
        {
            let val = self.az::<u64>();
            unsafe {
                val.copy(inner, limbs);
            }
        }
    }
}

impl ToSmall for f32 {}
impl SealedToSmall for f32 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = cast_ptr_mut!(limbs.as_mut_ptr(), limb_t);
        let val = self.into();
        let rnd = raw_round(Round::Nearest);
        unsafe {
            xmpfr::custom_zero(ptr, limbs_ptr, 24);
            mpfr::set_d(ptr, val, rnd);
        }
        // retain sign in case of NaN
        if self.is_sign_negative() {
            unsafe {
                (*inner).sign = -1;
            }
        }
    }
}

impl ToSmall for f64 {}
impl SealedToSmall for f64 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = cast_ptr_mut!(limbs.as_mut_ptr(), limb_t);
        let rnd = raw_round(Round::Nearest);
        unsafe {
            xmpfr::custom_zero(ptr, limbs_ptr, 53);
            mpfr::set_d(ptr, self, rnd);
        }
        // retain sign in case of NaN
        if self.is_sign_negative() {
            unsafe {
                (*inner).sign = -1;
            }
        }
    }
}

impl ToSmall for Special {}
impl SealedToSmall for Special {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = cast_ptr_mut!(limbs.as_mut_ptr(), limb_t);
        let prec = float::prec_min().az();
        unsafe {
            xmpfr::custom_special(ptr, limbs_ptr, self, prec);
        }
    }
}

impl<T: ToSmall> Assign<T> for SmallFloat {
    #[inline]
    fn assign(&mut self, src: T) {
        unsafe {
            src.copy(&mut self.inner, &mut self.limbs);
        }
    }
}

impl<T: ToSmall> From<T> for SmallFloat {
    #[inline]
    fn from(src: T) -> Self {
        let mut inner = Mpfr {
            prec: 0,
            sign: 0,
            exp: 0,
            d: UnsafeCell::new(NonNull::dangling()),
        };
        let mut limbs = small_limbs![];
        unsafe {
            src.copy(&mut inner, &mut limbs);
        }
        SmallFloat { inner, limbs }
    }
}

impl Assign<&Self> for SmallFloat {
    #[inline]
    fn assign(&mut self, other: &Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallFloat {
    #[inline]
    fn assign(&mut self, other: Self) {
        drop(mem::replace(self, other));
    }
}

#[inline]
pub(crate) unsafe fn unchecked_get_unshifted_u8(small: &SmallFloat) -> u8 {
    debug_assert!(small.prec() >= 8);
    debug_assert!(small.is_normal());
    (unsafe { small.limbs[0].assume_init() } >> (gmp::LIMB_BITS - 8)).wrapping_cast()
}

#[inline]
pub(crate) unsafe fn unchecked_get_unshifted_u16(small: &SmallFloat) -> u16 {
    debug_assert!(small.prec() >= 16);
    debug_assert!(small.is_normal());
    (unsafe { small.limbs[0].assume_init() } >> (gmp::LIMB_BITS - 16)).wrapping_cast()
}

#[inline]
pub(crate) unsafe fn unchecked_get_unshifted_u32(small: &SmallFloat) -> u32 {
    debug_assert!(small.prec() >= 32);
    debug_assert!(small.is_normal());
    #[cfg(gmp_limb_bits_32)]
    {
        unsafe { small.limbs[0].assume_init() }
    }
    #[cfg(gmp_limb_bits_64)]
    {
        (unsafe { small.limbs[0].assume_init() } >> 32).wrapping_cast()
    }
}

#[inline]
pub(crate) unsafe fn unchecked_get_unshifted_u64(small: &SmallFloat) -> u64 {
    debug_assert!(small.prec() >= 64);
    debug_assert!(small.is_normal());
    #[cfg(gmp_limb_bits_32)]
    {
        u64::from(unsafe { small.limbs[0].assume_init() })
            | (u64::from(unsafe { small.limbs[1].assume_init() }) << 32)
    }
    #[cfg(gmp_limb_bits_64)]
    {
        unsafe { small.limbs[0].assume_init() }
    }
}

#[inline]
pub(crate) unsafe fn unchecked_get_unshifted_u128(small: &SmallFloat) -> u128 {
    debug_assert!(small.prec() >= 128);
    debug_assert!(small.is_normal());
    #[cfg(gmp_limb_bits_32)]
    {
        u128::from(unsafe { small.limbs[0].assume_init() })
            | (u128::from(unsafe { small.limbs[1].assume_init() }) << 32)
            | (u128::from(unsafe { small.limbs[2].assume_init() }) << 64)
            | (u128::from(unsafe { small.limbs[3].assume_init() }) << 96)
    }
    #[cfg(gmp_limb_bits_64)]
    {
        u128::from(unsafe { small.limbs[0].assume_init() })
            | (u128::from(unsafe { small.limbs[1].assume_init() }) << 64)
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use crate::{
        float::{self, FreeCache, SmallFloat, Special},
        Assign,
    };

    #[test]
    fn check_assign() {
        let mut f = SmallFloat::from(-1.0f32);
        assert_eq!(*f, -1.0);
        f.assign(-2.0f64);
        assert_eq!(*f, -2.0);
        let other = SmallFloat::from(4u8);
        f.assign(&other);
        assert_eq!(*f, 4);
        f.assign(5i8);
        assert_eq!(*f, 5);
        f.assign(other);
        assert_eq!(*f, 4);
        f.assign(6u16);
        assert_eq!(*f, 6);
        f.assign(-6i16);
        assert_eq!(*f, -6);
        f.assign(6u32);
        assert_eq!(*f, 6);
        f.assign(-6i32);
        assert_eq!(*f, -6);
        f.assign(6u64);
        assert_eq!(*f, 6);
        f.assign(-6i64);
        assert_eq!(*f, -6);
        f.assign(6u128);
        assert_eq!(*f, 6);
        f.assign(-6i128);
        assert_eq!(*f, -6);
        f.assign(6usize);
        assert_eq!(*f, 6);
        f.assign(-6isize);
        assert_eq!(*f, -6);
        f.assign(0u32);
        assert_eq!(*f, 0);
        f.assign(Special::Infinity);
        assert!(f.is_infinite() && f.is_sign_positive());
        f.assign(Special::NegZero);
        assert!(f.is_zero() && f.is_sign_negative());
        f.assign(Special::NegInfinity);
        assert!(f.is_infinite() && f.is_sign_negative());
        f.assign(Special::Zero);
        assert!(f.is_zero() && f.is_sign_positive());
        f.assign(Special::Nan);
        assert!(f.is_nan());

        float::free_cache(FreeCache::All);
    }
}
