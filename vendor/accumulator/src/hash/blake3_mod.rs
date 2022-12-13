//! `GeneralHasher` interface for `blake3`.
use super::GeneralHasher;
use blake3::Hasher as Blake3_;
use std::hash::Hasher;

/// Thin wrapper around `Blake3` from `blake2_rfc`.
pub struct Blake3(pub Blake3_);

impl Default for Blake3 {
  #[inline]
  fn default() -> Self {
    // 32 bytes = 256 bits
    Self(Blake3_::new_derive_key("purplecoin.accumulator"))
  }
}

impl Hasher for Blake3 {
  /// We could return a truncated hash but it's easier just to not use this fn for now.
  fn finish(&self) -> u64 {
    panic!("Don't use! Prefer finalize(self).")
  }
  #[inline]
  fn write(&mut self, bytes: &[u8]) {
    Blake3_::update(&mut self.0, bytes);
  }
}

impl GeneralHasher for Blake3 {
  type Output = [u8; 32];
  #[inline]
  fn finalize(self) -> Self::Output {
    let res = self.0.finalize();
    *res.as_bytes()
  }
}
