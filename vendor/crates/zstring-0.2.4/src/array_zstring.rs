use crate::{CharDecoder, ZStr, ZStringError};

/// An array holding textual data that's zero termianted.
///
/// This is a newtype over a byte array, with a const generic length `N`.
///
/// The bytes contained *should* be utf-8 encoded, but the [`CharDecoder`] used
/// to convert the bytes to `char` values is safe to use even when the bytes are
/// not proper utf-8.
///
/// ## Safety
/// * The [`as_zstr`](ArrayZString<N>::as_zstr) method assumes that there's a
///   null somewhere before the end of the array. Safe code cannot break this
///   rule, but unsafe code must be sure to maintain this invaraint. The array
///   has size `N`, but only `N-1` of the bytes are usable, because there has to
///   be at least one `'\0'` before the end of the array.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct ArrayZString<const N: usize>([u8; N]);
impl<const N: usize> ArrayZString<N> {
  /// Gives a zeroed array.
  ///
  /// This is the same as [`default`](ArrayZString<N>::default), but `const fn`.
  #[inline]
  #[must_use]
  pub const fn const_default() -> Self {
    Self([0_u8; N])
  }

  /// Gets a [`ZStr`] to this data.
  ///
  /// ## Panics
  /// * If the length `N` is zero, this will panic.
  #[inline]
  #[must_use]
  pub const fn as_zstr(&self) -> ZStr<'_> {
    assert!(N > 0);
    unsafe { core::mem::transmute::<*const u8, ZStr<'_>>(self.0.as_ptr()) }
  }

  /// View the data as a rust `&str`.
  ///
  /// ## Panics
  /// * If somehow the bytes in the array aren't utf-8 this will panic. Safe
  ///   code cannot cause this to happen.
  #[inline]
  #[must_use]
  #[track_caller]
  pub fn as_str(&self) -> &str {
    let null_position = self.0.iter().position(|&b| b == 0).unwrap();
    core::str::from_utf8(&self.0[..null_position]).unwrap()
  }

  /// An iterator over the bytes of this `ZStr`.
  ///
  /// * This iterator *excludes* the terminating 0 byte.
  #[inline]
  pub fn bytes(&self) -> impl Iterator<Item = u8> + '_ {
    self.0.iter().copied().take_while(|&b| b != 0)
  }

  /// An iterator over the decoded `char` values of this `ZStr`.
  #[inline]
  pub fn chars(&self) -> impl Iterator<Item = char> + '_ {
    CharDecoder::from(self.bytes())
  }

  /// Gets the raw pointer to this data.
  #[inline]
  #[must_use]
  pub const fn as_ptr(self) -> *const u8 {
    self.0.as_ptr()
  }
}
impl<const N: usize> Default for ArrayZString<N> {
  #[inline]
  #[must_use]
  fn default() -> Self {
    Self::const_default()
  }
}
impl<const N: usize> TryFrom<&str> for ArrayZString<N> {
  type Error = Option<ZStringError>;
  /// Attempts to make an `ArrayZString` from a `&str`
  ///
  /// ```
  /// # use zstring::*;
  /// let arr_str: ArrayZString<16> = ArrayZString::try_from("hello").unwrap();
  /// assert_eq!(arr_str.as_str(), "hello");
  /// ```
  ///
  /// ## Failure
  /// The error type is unfortunately awkward here because 0.2 released with an
  /// exhaustive error type. So instead we get an `Option<ZStringError>`, where
  /// `Some` is an actual [`ZStringError`] and `None` indicates that there was
  /// no zstring related issue, just a lack of capacity.
  ///
  /// * Any number of trailing nulls are allowed, and will be trimmed.
  /// * Interior nulls are not allowed (err:
  ///   `Some(ZStringError::InteriorNulls)`).
  /// * The trimmed byte length must be less than or equal to `N-1` (err:
  ///   `None`).
  ///
  /// ```
  /// # use zstring::*;
  /// let interior_null_err: Option<ZStringError> =
  ///   ArrayZString::<16>::try_from("hel\0lo").unwrap_err();
  /// assert_eq!(interior_null_err, Some(ZStringError::InteriorNulls));
  ///
  /// // strings equal to or greater than the array size won't fit.
  /// let capacity_err: Option<ZStringError> =
  ///   ArrayZString::<5>::try_from("hello").unwrap_err();
  /// assert_eq!(capacity_err, None);
  ///
  /// // if the array size exceeds the string size it will fit.
  /// assert!(ArrayZString::<6>::try_from("hello").is_ok());
  /// ```
  #[inline]
  fn try_from(value: &str) -> Result<Self, Self::Error> {
    let trimmed = value.trim_end_matches('\0');
    if trimmed.as_bytes().iter().copied().any(|b| b == 0) {
      Err(Some(ZStringError::InteriorNulls))
    } else if trimmed.len() <= (N - 1) {
      let mut out = Self::const_default();
      out.0[..trimmed.len()].copy_from_slice(trimmed.as_bytes());
      Ok(out)
    } else {
      Err(None)
    }
  }
}
impl<const N: usize> core::fmt::Display for ArrayZString<N> {
  /// Display formats the string (without outer `"`).
  ///
  /// ```rust
  /// # use zstring::*;
  /// let arr_str: ArrayZString<16> = ArrayZString::try_from("foo").unwrap();
  /// let s = format!("{arr_str}");
  /// assert_eq!("foo", s);
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Display::fmt(&self.as_zstr(), f)
  }
}
impl<const N: usize> core::fmt::Debug for ArrayZString<N> {
  /// Debug formats with outer `"` around the string.
  ///
  /// ```rust
  /// # use zstring::*;
  /// let arr_str: ArrayZString<16> = ArrayZString::try_from("foo").unwrap();
  /// let s = format!("{arr_str:?}");
  /// assert_eq!("\"foo\"", s);
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Debug::fmt(&self.as_zstr(), f)
  }
}

impl<const N: usize, const X: usize> PartialEq<ArrayZString<X>>
  for ArrayZString<N>
{
  /// Two `ArrayZString` are equal when the bytes "in" their strings are the
  /// same, regardless of capacity differences.
  ///
  /// ```
  /// # use zstring::*;
  /// assert_eq!(
  ///   ArrayZString::<6>::try_from("hello").unwrap(),
  ///   ArrayZString::<10>::try_from("hello").unwrap(),
  /// );
  /// ```
  #[inline]
  #[must_use]
  fn eq(&self, other: &ArrayZString<X>) -> bool {
    self.bytes().eq(other.bytes())
  }
}
impl<const N: usize, const X: usize> PartialOrd<ArrayZString<X>>
  for ArrayZString<N>
{
  /// Two `ArrayZString` are compared by the bytes "in" their strings,
  /// regardless of capacity differences.
  ///
  /// ```
  /// # use zstring::*;
  /// # use core::cmp::{PartialOrd, Ordering};
  /// let abc = ArrayZString::<6>::try_from("abc").unwrap();
  /// let def = ArrayZString::<10>::try_from("def").unwrap();
  /// assert_eq!(abc.partial_cmp(&def), Some(Ordering::Less));
  /// ```
  #[inline]
  #[must_use]
  fn partial_cmp(
    &self, other: &ArrayZString<X>,
  ) -> Option<core::cmp::Ordering> {
    Some(self.bytes().cmp(other.bytes()))
  }
}

impl<const N: usize> Eq for ArrayZString<N> {}
impl<const N: usize> Ord for ArrayZString<N> {
  #[inline]
  #[must_use]
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.partial_cmp(other).unwrap()
  }
}

impl<const N: usize> PartialEq<ZStr<'_>> for ArrayZString<N> {
  /// An `ArrayZString<N>` equals a `ZStr` by bytes.
  #[inline]
  #[must_use]
  fn eq(&self, other: &ZStr<'_>) -> bool {
    self.bytes().eq(other.bytes())
  }
}
impl<const N: usize> PartialOrd<ZStr<'_>> for ArrayZString<N> {
  /// An `ArrayZString<N>` compares to a `ZStr` by bytes.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &ZStr<'_>) -> Option<core::cmp::Ordering> {
    Some(self.bytes().cmp(other.bytes()))
  }
}

#[cfg(feature = "alloc")]
impl<const N: usize> PartialEq<crate::ZString> for ArrayZString<N> {
  /// An `ArrayZString<N>` equals a `ZString` when they contain the same bytes.
  #[inline]
  #[must_use]
  fn eq(&self, other: &crate::ZString) -> bool {
    self.eq(&other.as_zstr())
  }
}
#[cfg(feature = "alloc")]
impl<const N: usize> PartialOrd<crate::ZString> for ArrayZString<N> {
  /// An `ArrayZString<N>` compares to a `ZString` by bytes.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &crate::ZString) -> Option<core::cmp::Ordering> {
    self.partial_cmp(&other.as_zstr())
  }
}

impl<const N: usize> core::hash::Hash for ArrayZString<N> {
  #[inline]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    for b in self.bytes() {
      state.write_u8(b)
    }
  }
}
