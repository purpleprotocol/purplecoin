#![no_std]
#![warn(missing_docs)]
#![forbid(unsafe_code)]
#![warn(clippy::missing_const_for_fn)]
#![warn(clippy::missing_inline_in_public_items)]

//! Provides [Bool32], which is a 32-bit bool-ish type.
//!
//! This is primarily of use with FFI, because APIs in C often use an int as
//! their true/false type.

/// A 32-bit bool-ish type.
///
/// This is `repr(transparent)` and wraps a `u32`. When the value is 0 it's
/// "false" and when the value is non-zero it's "true". The methods of this type
/// only ever allow the wrapped value to be 0 or 1, but if you make this type
/// interact with foreign functions they could produce other non-zero values. It
/// is *not* an absolute invariant of this type that the wrapped value always be
/// exactly 0 or 1, the wrapped value can be any value.
///
/// For readability, the type formats with [Debug](core::fmt::Debug) and
/// [Display](core::fmt::Display) just like a [bool], showing as either `true`
/// or `false`.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Bool32(u32);
impl Bool32 {
  /// Constant for the `false` value.
  pub const FALSE: Self = Self::new(false);

  /// Constant for the canonical `true` value.
  ///
  /// Note that *any* non-zero wrapped value is considered to be "true", this is
  /// just the canonical true value (1).
  pub const TRUE: Self = Self::new(true);

  /// Like `Bool32::from(bool)`, but `const fn`.
  ///
  /// ```
  /// # use bool32::*;
  /// const F: Bool32 = Bool32::new(false);
  /// const T: Bool32 = Bool32::new(true);
  /// assert_eq!(F, Bool32::FALSE);
  /// assert_eq!(T, Bool32::TRUE);
  /// ```
  #[inline]
  #[must_use]
  pub const fn new(b: bool) -> Self {
    Self(b as _)
  }
}

impl From<bool> for Bool32 {
  /// ```
  /// # use bool32::*;
  /// assert!(bool::from(Bool32::new(true)));
  /// assert!(!bool::from(Bool32::new(false)));
  /// ```
  #[inline]
  #[must_use]
  fn from(value: bool) -> Self {
    Self(value as _)
  }
}
impl From<Bool32> for bool {
  /// ```
  /// # use bool32::*;
  /// assert_eq!(Bool32::from(true), Bool32::TRUE);
  /// assert_eq!(Bool32::from(false), Bool32::FALSE);
  /// ```
  #[inline]
  #[must_use]
  fn from(value: Bool32) -> Self {
    value.0 != 0
  }
}

impl core::fmt::Debug for Bool32 {
  /// ```
  /// # use bool32::*;
  /// assert_eq!(format!("{:?}", true), format!("{:?}", Bool32::TRUE));
  /// assert_eq!(format!("{:?}", false), format!("{:?}", Bool32::FALSE));
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Debug::fmt(&bool::from(*self), f)
  }
}
impl core::fmt::Display for Bool32 {
  /// ```
  /// # use bool32::*;
  /// assert_eq!(format!("{}", true), format!("{}", Bool32::TRUE));
  /// assert_eq!(format!("{}", false), format!("{}", Bool32::FALSE));
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Display::fmt(&bool::from(*self), f)
  }
}
