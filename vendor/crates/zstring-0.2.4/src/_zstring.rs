use core::{marker::PhantomData, mem::ManuallyDrop, ptr::NonNull};

use alloc::{boxed::Box, string::String, vec::Vec};

use crate::{ZStr, ZStringError};

/// Owning and non-null pointer to zero-terminated textual data.
///
/// Because this is a thin pointer it's suitable for direct FFI usage.
///
/// The bytes pointed to *should* be utf-8 encoded, but the [`CharDecoder`] used
/// to convert the bytes to `char` values is safe to use even when the bytes are
/// not proper utf-8.
///
/// ## Safety
/// * This is `repr(transparent)` over a [`NonNull<u8>`].
/// * The wrapped pointer points at a sequence of valid-to-read non-zero byte
///   values followed by at least one zero byte.
/// * The `ZString` owns the data, and will free it on drop.
#[repr(transparent)]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub struct ZString {
  pub(crate) nn: NonNull<u8>,
}
impl Drop for ZString {
  #[inline]
  fn drop(&mut self) {
    let len = 1 + self.bytes().count();
    let slice_ptr: *mut [u8] =
      core::ptr::slice_from_raw_parts_mut(self.nn.as_ptr(), len);
    drop(unsafe { Box::from_raw(slice_ptr) })
  }
}
impl Clone for ZString {
  /// Clones the value
  ///
  /// ```
  /// # use zstring::*;
  /// //
  /// let zstring1 = ZString::try_from("abc").unwrap();
  /// let zstring2 = zstring1.clone();
  /// assert!(zstring1.chars().eq(zstring2.chars()));
  /// ```
  #[inline]
  #[must_use]
  fn clone(&self) -> Self {
    let len = 1 + self.bytes().count();
    let slice_ptr: &[u8] =
      unsafe { core::slice::from_raw_parts(self.nn.as_ptr(), len) };
    let vec = Vec::from(slice_ptr);
    // Safety: we know this will be utf-8 data because you can only safely
    // create a `ZString` from utf-8 sources (`&str` and `String`).
    let string = unsafe { String::from_utf8_unchecked(vec) };
    let boxed_str = string.into_boxed_str();
    // Safety: This data is cloned from an existing `ZString`.
    unsafe { Self::new_unchecked(boxed_str) }
  }
}
impl ZString {
  /// Converts a [`Box<str>`] into a [`ZString`] without any additional
  /// checking.
  ///
  /// ## Safety
  /// * The data **must** have *exactly* one null byte at the end.
  /// * The data **must not** contain interior null bytes.
  ///
  /// Breaking either of the above rules will cause the wrong amount to be freed
  /// when the `ZString` drops.
  #[inline]
  #[must_use]
  pub unsafe fn new_unchecked(b: Box<str>) -> Self {
    let p: *mut u8 = Box::leak(b).as_mut_ptr();
    let nn: NonNull<u8> = unsafe { NonNull::new_unchecked(p) };
    Self { nn }
  }

  /// Borrows this `ZString` as a `ZStr`.
  #[inline]
  #[must_use]
  pub const fn as_zstr(&self) -> ZStr<'_> {
    ZStr { nn: self.nn, life: PhantomData }
  }

  /// Gets the raw pointer to this data.
  #[inline]
  #[must_use]
  pub const fn as_ptr(&self) -> *const u8 {
    self.nn.as_ptr()
  }

  /// An iterator over the bytes of this `ZStr`.
  ///
  /// * This iterator *excludes* the terminating 0 byte.
  #[inline]
  pub fn bytes(&self) -> impl Iterator<Item = u8> + '_ {
    self.as_zstr().bytes()
  }

  /// An iterator over the decoded `char` values of this `ZStr`.
  #[inline]
  pub fn chars(&self) -> impl Iterator<Item = char> + '_ {
    self.as_zstr().chars()
  }
}
impl From<ZStr<'_>> for ZString {
  /// This is like a "to owned' style operation.
  ///
  /// ```rust
  /// # use zstring::*;
  /// const FOO: ZStr<'static> = ZStr::from_lit("foo\0");
  /// let zstring = ZString::from(FOO);
  /// assert_eq!(zstring, FOO);
  /// ```
  #[inline]
  #[must_use]
  fn from(value: ZStr<'_>) -> Self {
    let other: ManuallyDrop<ZString> =
      ManuallyDrop::new(ZString { nn: value.nn });
    let other_ref: &ZString = &other;
    other_ref.clone()
  }
}
impl FromIterator<char> for ZString {
  #[inline]
  fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
    let iter = iter.into_iter();
    let no_nulls = iter.map(|ch| {
      assert_ne!(ch, '\0');
      ch
    });
    let null_on_the_end = no_nulls.chain(['\0']);
    let s = String::from_iter(null_on_the_end);
    // Safety: We've ensures that there's no nulls within the source iteration,
    // and that we've added a single null to the end of the iteration.
    unsafe { ZString::new_unchecked(s.into_boxed_str()) }
  }
}
impl TryFrom<&str> for ZString {
  type Error = ZStringError;
  /// Trims any trailing nulls and then makes a [`ZString`] from what's left.
  ///
  /// ```
  /// # use zstring::*;
  /// let zstring1 = ZString::try_from("abc").unwrap();
  /// assert!("abc".chars().eq(zstring1.chars()));
  ///
  /// let zstring2 = ZString::try_from("foo\0\0\0\0").unwrap();
  /// assert!("foo".chars().eq(zstring2.chars()));
  /// ```
  ///
  /// ## Failure
  /// * If there are any interior nulls.
  ///
  /// ```
  /// # use zstring::*;
  /// assert!(ZString::try_from("ab\0c").is_err());
  /// ```
  #[inline]
  fn try_from(value: &str) -> Result<Self, Self::Error> {
    let trimmed = value.trim_end_matches('\0');
    if trimmed.contains('\0') {
      Err(ZStringError::InteriorNulls)
    } else {
      Ok(trimmed.chars().collect())
    }
  }
}
impl core::fmt::Display for ZString {
  /// Display formats the string (without outer `"`).
  ///
  /// ```rust
  /// # use zstring::*;
  /// let zstring = ZString::try_from("foo").unwrap();
  /// let s = format!("{zstring}");
  /// assert_eq!("foo", s);
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Display::fmt(&self.as_zstr(), f)
  }
}
impl core::fmt::Debug for ZString {
  /// Debug formats with outer `"` around the string.
  ///
  /// ```rust
  /// # use zstring::*;
  /// let zstring = ZString::try_from("foo").unwrap();
  /// let s = format!("{zstring:?}");
  /// assert_eq!("\"foo\"", s);
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Debug::fmt(&self.as_zstr(), f)
  }
}
impl core::fmt::Pointer for ZString {
  /// Formats the wrapped pointer value.
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Pointer::fmt(&self.as_zstr(), f)
  }
}

impl PartialEq<ZString> for ZString {
  /// Two `ZString` are considered equal if they point at the exact same *byte
  /// sequence*.
  ///
  /// This is much faster to compute when the bytes are valid UTF-8, though it
  /// is stricter if the bytes are not valid UTF-8 (the character replacement
  /// process during decoding *could* make two different byte sequences have the
  /// same character sequence).
  #[inline]
  #[must_use]
  fn eq(&self, other: &ZString) -> bool {
    self.as_zstr().eq(&other.as_zstr())
  }
}
impl PartialOrd<ZString> for ZString {
  /// Compares based on the *byte sequence* pointed to.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &ZString) -> Option<core::cmp::Ordering> {
    self.as_zstr().partial_cmp(&other.as_zstr())
  }
}

impl PartialEq<&str> for ZString {
  /// A `ZStr` equals a `&str` if the bytes match.
  #[inline]
  #[must_use]
  fn eq(&self, other: &&str) -> bool {
    self.bytes().eq(other.as_bytes().iter().copied())
  }
}
impl PartialOrd<&str> for ZString {
  /// Compares based on the *byte sequence* pointed to.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &&str) -> Option<core::cmp::Ordering> {
    Some(self.bytes().cmp(other.as_bytes().iter().copied()))
  }
}

impl PartialEq<ZStr<'_>> for ZString {
  /// A `ZString` equals a `ZStr` by calling `ZString::as_zstr`
  #[inline]
  #[must_use]
  fn eq(&self, other: &ZStr<'_>) -> bool {
    self.as_zstr().eq(other)
  }
}
impl PartialOrd<ZStr<'_>> for ZString {
  /// Compares based on the *byte sequence* pointed to.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &ZStr<'_>) -> Option<core::cmp::Ordering> {
    self.as_zstr().partial_cmp(other)
  }
}

impl core::hash::Hash for ZString {
  #[inline]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    for b in self.bytes() {
      state.write_u8(b)
    }
  }
}

/// Re-view a slice of [ZString] as a slice of [ZStr]
///
/// ```
/// # use zstring::*;
/// let zstrings =
///   [ZString::try_from("hello").unwrap(), ZString::try_from("world").unwrap()];
/// let s: &[ZStr<'_>] = zstrings_as_zstrs(&zstrings);
/// let mut iter = s.iter();
/// assert!("hello".chars().eq(iter.next().unwrap().chars()));
/// assert!("world".chars().eq(iter.next().unwrap().chars()));
/// ```
#[inline]
#[must_use]
pub fn zstrings_as_zstrs(zstrings: &[ZString]) -> &[ZStr<'_>] {
  // Safety: The two types have identical layout.
  // what differs is that one is borrowed and one
  // is owned. However, behind a slice reference that
  // doesn't have any significance.
  unsafe {
    core::slice::from_raw_parts(zstrings.as_ptr().cast(), zstrings.len())
  }
}
