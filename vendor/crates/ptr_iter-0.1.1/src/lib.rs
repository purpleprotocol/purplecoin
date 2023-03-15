#![no_std]
#![warn(missing_docs)]

//! A crate with iterators to simplify working with pointers.
//!
//! Constructing these iterators is unsafe, but once constructed the iteration
//! itself is considered a safe operation.
//!
//! The two iterators themselves will iterate forever. The constructor functions
//! apply the correct iterator adapters to limit the iteration to stay within
//! safe bounds.
//!
//! ## Safety
//! * You must always use the iterator before the pointer it's based upon
//!   becomes invalidated. This is the same logic as constructing a slice from a
//!   raw pointer: If you use a pointer to build a safe type and then invalidate
//!   the source pointer, the safe type itself will become invalid too.
//! * The iteration is done with the pointer [`add`](https://doc.rust-lang.org/nightly/std/primitive.pointer.html#method.add)
//!   method, and so these iterators must only be constructed with pointers to
//!   valid allocations.

/// An iterator based on a mutable pointer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct MutPtrIter<T>(*mut T);
impl<T> Iterator for MutPtrIter<T> {
  type Item = *mut T;
  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let out = self.0;
    self.0 = unsafe { self.0.add(1) };
    Some(out)
  }
  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (usize::MAX, None)
  }
}
impl<T> MutPtrIter<T> {
  /// Iterates all pointers within the slice pointer given.
  ///
  /// ```rust
  /// # use ptr_iter::MutPtrIter;
  /// let mut arr: [u8; 4] = [5, 6, 7, 8];
  /// let mut iter = unsafe { MutPtrIter::over_slice_ptr(&mut arr).map(|p| *p) };
  /// assert_eq!(iter.next(), Some(5_u8));
  /// assert_eq!(iter.next(), Some(6_u8));
  /// assert_eq!(iter.next(), Some(7_u8));
  /// assert_eq!(iter.next(), Some(8_u8));
  /// assert_eq!(iter.next(), None);
  /// assert_eq!(iter.next(), None);
  /// ```
  ///
  /// ## Safety
  /// * The slice pointer must point to a valid allocation.
  /// * You agree ahead of time to not use the iterator after the pointer is
  ///   invalid.
  #[inline]
  pub unsafe fn over_slice_ptr(p: *mut [T]) -> core::iter::Take<Self> {
    // Safety: the caller has to pass a valid pointer, so we can use
    // new_unchecked because a null pointer is never valid. This appears to be
    // the only stable way to get a slice pointer's length.
    let len: usize = core::ptr::NonNull::new_unchecked(p).len();
    Self(p as *mut T).take(len)
  }
}

/// An iterator based on a constant pointer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct ConstPtrIter<T>(*const T);
impl<T> Iterator for ConstPtrIter<T> {
  type Item = *const T;
  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    let out = self.0;
    self.0 = unsafe { self.0.add(1) };
    Some(out)
  }
  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (usize::MAX, None)
  }
}
impl<T> ConstPtrIter<T> {
  /// Iterates all pointers within the slice pointer given.
  ///
  /// ```rust
  /// # use ptr_iter::ConstPtrIter;
  /// let arr: [u8; 4] = [5, 6, 7, 8];
  /// let mut iter = unsafe { ConstPtrIter::over_slice_ptr(&arr).map(|p| *p) };
  /// assert_eq!(iter.next(), Some(5_u8));
  /// assert_eq!(iter.next(), Some(6_u8));
  /// assert_eq!(iter.next(), Some(7_u8));
  /// assert_eq!(iter.next(), Some(8_u8));
  /// assert_eq!(iter.next(), None);
  /// assert_eq!(iter.next(), None);
  /// ```
  ///
  /// ## Safety
  /// * The slice pointer must point to a valid allocation.
  /// * You agree ahead of time to not use the iterator after the pointer is
  ///   invalid.
  #[inline]
  pub unsafe fn over_slice_ptr(p: *const [T]) -> core::iter::Take<Self> {
    // Safety: the caller has to pass a valid pointer, so we can use
    // new_unchecked because a null pointer is never valid. This appears to be
    // the only stable way to get a slice pointer's length.
    let len: usize = core::ptr::NonNull::new_unchecked(p as *mut [T]).len();
    Self(p as *const T).take(len)
  }

  /// Reads successive pointer positions and returns values until the type's
  /// default value is read.
  ///
  /// * The default value is *excluded* from the iterator's output sequence.
  ///
  /// This covers the common case of iterating "C String" style data, where the
  /// data consists of an unknown number of non-zero elements and then a 0
  /// marking the end of the sequence.
  ///
  /// ```rust
  /// # use ptr_iter::ConstPtrIter;
  /// let arr: &[u8; 5] = b"rust\0";
  /// let mut iter = unsafe { ConstPtrIter::read_until_default(arr.as_ptr()) };
  /// assert_eq!(iter.next(), Some(b'r'));
  /// assert_eq!(iter.next(), Some(b'u'));
  /// assert_eq!(iter.next(), Some(b's'));
  /// assert_eq!(iter.next(), Some(b't'));
  /// assert_eq!(iter.next(), None);
  /// assert_eq!(iter.next(), None);
  /// ```
  ///
  /// ## Safety
  /// * The pointer must be valid for reads up to and including the position of
  ///   the default element.
  /// * You agree ahead of time to not use the iterator after the pointer is
  ///   invalid.
  #[inline]
  pub unsafe fn read_until_default(
    p: *const T,
  ) -> impl Iterator<Item = T> + Clone
  where
    T: Copy + Default + PartialEq,
  {
    Self(p).map(|p| unsafe { *p }).take_while(|p| p != &T::default())
  }
}
