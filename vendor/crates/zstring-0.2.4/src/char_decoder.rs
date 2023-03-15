#![forbid(unsafe_code)]

/// Decodes byte sequences as if they were utf-8.
///
/// If the bytes are not utf-8 you'll automatically get the
/// [`REPLACEMENT_CHARACTER`](char::REPLACEMENT_CHARACTER) within the output, as
/// necessary.
///
/// Construct this iterator using `from` on any other iterator over `u8`.
///
/// ```rust
/// # use zstring::CharDecoder;
/// let decoder1 = CharDecoder::from([32, 33, 34].into_iter());
/// let decoder2 = CharDecoder::from("foobar".as_bytes().iter().copied());
/// ```
pub struct CharDecoder<I: Iterator<Item = u8>> {
  iter: core::iter::Peekable<I>,
}
impl<I: Iterator<Item = u8>> From<I> for CharDecoder<I> {
  #[inline]
  #[must_use]
  fn from(i: I) -> Self {
    Self { iter: i.peekable() }
  }
}
impl<I: Iterator<Item = u8>> CharDecoder<I> {
  /// Returns the next continuation bits (pre-masked), only if the next byte is
  /// a continuation byte.
  #[inline]
  #[must_use]
  fn next_continuation_bits(&mut self) -> Option<u32> {
    match self.iter.peek()? {
      x if x >> 6 == 0b10 => Some((self.iter.next()? as u32) & 0b111111),
      _ => None,
    }
  }
}
impl<I: Iterator<Item = u8>> Iterator for CharDecoder<I> {
  type Item = char;

  #[inline]
  #[must_use]
  fn next(&mut self) -> Option<char> {
    let x = u32::from(self.iter.next()?);
    if x < 128 {
      // fast path for ascii
      Some(x as u8 as char)
    } else {
      match UTF8_CHAR_WIDTH[x as usize] {
        2 => {
          let Some(y) = self.next_continuation_bits() else {
            return Some(char::REPLACEMENT_CHARACTER);
          };
          let u = ((x & 0b11111) << 6) | y;
          Some(char::from_u32(u).unwrap_or(char::REPLACEMENT_CHARACTER))
        }
        3 => {
          let Some(y) = self.next_continuation_bits() else {
            return Some(char::REPLACEMENT_CHARACTER);
          };
          let Some(z) = self.next_continuation_bits() else {
            return Some(char::REPLACEMENT_CHARACTER);
          };
          let u = ((x & 0b1111) << 12) | y << 6 | z;
          Some(char::from_u32(u).unwrap_or(char::REPLACEMENT_CHARACTER))
        }
        4 => {
          let Some(y) = self.next_continuation_bits() else {
            return Some(char::REPLACEMENT_CHARACTER);
          };
          let Some(z) = self.next_continuation_bits() else {
            return Some(char::REPLACEMENT_CHARACTER);
          };
          let Some(w) = self.next_continuation_bits() else {
            return Some(char::REPLACEMENT_CHARACTER);
          };
          let u = ((x & 0b111) << 18) | y << 12 | z << 6 | w;
          Some(char::from_u32(u).unwrap_or(char::REPLACEMENT_CHARACTER))
        }
        _ => Some(char::REPLACEMENT_CHARACTER),
      }
    }
  }
}

/// You can't copyright facts
const UTF8_CHAR_WIDTH: &[u8; 256] = &[
  // 1  2  3  4  5  6  7  8  9  A  B  C  D  E  F
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 0
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 1
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 2
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 3
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 4
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 5
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 6
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 7
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 8
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 9
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // A
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // B
  0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // C
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // D
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // E
  4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // F
];
