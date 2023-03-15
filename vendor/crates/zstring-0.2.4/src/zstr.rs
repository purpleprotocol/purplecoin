use super::*;
use core::{cmp::Ordering, fmt::Write, marker::PhantomData, ptr::NonNull};

/// Borrowed and non-null pointer to zero-terminated text data.
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
/// * When you create a `ZStr<'a>` value the pointer must be valid for at least
///   as long as the lifetime `'a`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct ZStr<'a> {
  pub(crate) nn: NonNull<u8>,
  pub(crate) life: PhantomData<&'a [u8]>,
}
impl<'a> ZStr<'a> {
  /// Makes a `ZStr<'static>` from a `&'static str`
  ///
  /// This is *intended* for use with string litearls, but if you leak a runtime
  /// string into a static string I guess that works too.
  ///
  /// ```rust
  /// # use zstring::*;
  /// const FOO: ZStr<'static> = ZStr::from_lit("foo\0");
  /// ```
  ///
  /// ## Panics
  /// * If `try_from` would return an error, this will panic instead. Because
  ///   this is intended for compile time constants, the panic will "just"
  ///   trigger a build error.
  #[inline]
  #[track_caller]
  pub const fn from_lit(s: &'static str) -> ZStr<'static> {
    let bytes = s.as_bytes();
    let mut tail_index = bytes.len() - 1;
    while bytes[tail_index] == 0 {
      tail_index -= 1;
    }
    assert!(tail_index < bytes.len() - 1, "No trailing nulls.");
    let mut i = 0;
    while i < tail_index {
      if bytes[i] == 0 {
        panic!("Input contains interior null.");
      }
      i += 1;
    }
    ZStr {
      // Safety: References can't ever be null.
      nn: unsafe { NonNull::new_unchecked(s.as_ptr() as *mut u8) },
      life: PhantomData,
    }
  }

  /// An iterator over the bytes of this `ZStr`.
  ///
  /// * This iterator **excludes** the terminating 0 byte.
  #[inline]
  pub fn bytes(self) -> impl Iterator<Item = u8> + 'a {
    // Safety: per the type safety docs, whoever made this `ZStr` promised that
    // we can read the pointer's bytes until we find a 0 byte.
    unsafe { ConstPtrIter::read_until_default(self.nn.as_ptr()) }
  }

  /// An iterator over the decoded `char` values of this `ZStr`.
  #[inline]
  pub fn chars(self) -> impl Iterator<Item = char> + 'a {
    CharDecoder::from(self.bytes())
  }

  /// Gets the raw pointer to this data.
  #[inline]
  #[must_use]
  pub const fn as_ptr(self) -> *const u8 {
    self.nn.as_ptr()
  }
}
impl<'a> TryFrom<&'a str> for ZStr<'a> {
  type Error = ZStringError;
  /// Converts the value in place.
  ///
  /// The trailing nulls of the source `&str` will not "be in" the output
  /// sequence of the returned `ZStr`.
  ///
  /// ```rust
  /// # use zstring::*;
  /// let z1 = ZStr::try_from("abcd\0").unwrap();
  /// assert!(z1.chars().eq("abcd".chars()));
  ///
  /// let z2 = ZStr::try_from("abcd\0\0\0").unwrap();
  /// assert!(z2.chars().eq("abcd".chars()));
  /// ```
  ///
  /// ## Failure
  /// * There must be at least one trailing null in the input `&str`.
  /// * There must be no nulls followed by a non-null ("interior nulls"). This
  ///   second condition is not a strict requirement of the type, more of a
  ///   correctness lint. If interior nulls were allowed then `"ab\0cd\0"`
  ///   converted to a `ZStr` would only be read as `"ab"`, and the second half
  ///   of the string would effectively be erased.
  #[inline]
  fn try_from(value: &'a str) -> Result<Self, Self::Error> {
    let trimmed = value.trim_end_matches('\0');
    if value.len() == trimmed.len() {
      Err(ZStringError::NoTrailingNulls)
    } else if trimmed.contains('\0') {
      Err(ZStringError::InteriorNulls)
    } else {
      // Note: We have verified that the starting `str` value contains at
      // least one 0 byte.
      Ok(Self {
        nn: NonNull::new(value.as_ptr() as *mut u8).unwrap(),
        life: PhantomData,
      })
    }
  }
}
impl core::fmt::Display for ZStr<'_> {
  /// Display formats the string (without outer `"`).
  ///
  /// ```rust
  /// # use zstring::*;
  /// const FOO: ZStr<'static> = ZStr::from_lit("foo\0");
  /// let s = format!("{FOO}");
  /// assert_eq!(s, "foo");
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    for ch in self.chars() {
      write!(f, "{ch}")?;
    }
    Ok(())
  }
}
impl core::fmt::Debug for ZStr<'_> {
  /// Debug formats with outer `"` around the string.
  ///
  /// ```rust
  /// # use zstring::*;
  /// const FOO: ZStr<'static> = ZStr::from_lit("foo\0");
  /// let s = format!("{FOO:?}");
  /// assert_eq!(s, "\"foo\"");
  /// ```
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.write_char('"')?;
    core::fmt::Display::fmt(self, f)?;
    f.write_char('"')?;
    Ok(())
  }
}
impl core::fmt::Pointer for ZStr<'_> {
  /// Formats the wrapped pointer value.
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Pointer::fmt(&self.nn, f)
  }
}

impl PartialEq<ZStr<'_>> for ZStr<'_> {
  /// Two `ZStr` are considered equal if they point at the exact same *byte
  /// sequence*.
  ///
  /// This is much faster to compute when the bytes are valid UTF-8, though it
  /// is stricter if the bytes are not valid UTF-8 (the character replacement
  /// process during decoding *could* make two different byte sequences have the
  /// same character sequence).
  ///
  /// ```rust
  /// # use zstring::*;
  /// const FOO1: ZStr<'static> = ZStr::from_lit("foo\0");
  /// const FOO2: ZStr<'static> = ZStr::from_lit("foo\0");
  /// assert_eq!(FOO1, FOO2);
  /// ```
  #[inline]
  #[must_use]
  fn eq(&self, other: &ZStr<'_>) -> bool {
    if self.nn == other.nn {
      true
    } else {
      self.bytes().eq(other.bytes())
    }
  }
}
impl PartialOrd<ZStr<'_>> for ZStr<'_> {
  /// Compares based on the *byte sequence* pointed to.
  ///
  /// ```rust
  /// # use zstring::*;
  /// # use core::cmp::{PartialOrd, Ordering};
  /// const ABC: ZStr<'static> = ZStr::from_lit("abc\0");
  /// const DEF: ZStr<'static> = ZStr::from_lit("def\0");
  /// const GHI: ZStr<'static> = ZStr::from_lit("ghi\0");
  /// assert_eq!(ABC.partial_cmp(&DEF), Some(Ordering::Less));
  /// assert_eq!(DEF.partial_cmp(&GHI), Some(Ordering::Less));
  /// assert_eq!(GHI.partial_cmp(&ABC), Some(Ordering::Greater));
  /// ```
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &ZStr<'_>) -> Option<core::cmp::Ordering> {
    if self.nn == other.nn {
      Some(Ordering::Equal)
    } else {
      Some(self.bytes().cmp(other.bytes()))
    }
  }
}

impl PartialEq<&str> for ZStr<'_> {
  /// A `ZStr` equals a `&str` if the bytes match.
  #[inline]
  #[must_use]
  fn eq(&self, other: &&str) -> bool {
    self.bytes().eq(other.as_bytes().iter().copied())
  }
}
impl PartialOrd<&str> for ZStr<'_> {
  /// Compares based on the *byte sequence* pointed to.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &&str) -> Option<core::cmp::Ordering> {
    Some(self.bytes().cmp(other.as_bytes().iter().copied()))
  }
}

#[cfg(feature = "alloc")]
impl PartialEq<ZString> for ZStr<'_> {
  /// A `ZStr` equals a `ZString` by calling `ZString::as_zstr`
  #[inline]
  #[must_use]
  fn eq(&self, other: &ZString) -> bool {
    self.eq(&other.as_zstr())
  }
}
#[cfg(feature = "alloc")]
impl PartialOrd<ZString> for ZStr<'_> {
  /// Compares based on the *byte sequence* pointed to.
  #[inline]
  #[must_use]
  fn partial_cmp(&self, other: &ZString) -> Option<core::cmp::Ordering> {
    self.partial_cmp(&other.as_zstr())
  }
}

impl core::hash::Hash for ZStr<'_> {
  #[inline]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    for b in self.bytes() {
      state.write_u8(b)
    }
  }
}

/// An error occurred while trying to make a [`ZStr`] or [`ZString`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZStringError {
  /// The provided data didn't have any trailing nulls (`'\0'`).
  NoTrailingNulls,
  /// The provided data had interior nulls (non-null data *after* a null).
  InteriorNulls,
}
