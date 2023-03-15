#![no_std]
#![warn(missing_docs)]
#![cfg_attr(docs_rs, feature(doc_cfg))]
#![warn(clippy::missing_inline_in_public_items)]

//! A crate for "thin pointer" zero-termianted string data.
//!
//! Unlike the [`CStr`](core::ffi::CStr) and [`CString`](alloc::ffi::CString)
//! types, these types are compatible with direct FFI usage.

#[cfg(feature = "alloc")]
extern crate alloc;

use ptr_iter::*;

mod char_decoder;
pub use char_decoder::*;

mod zstr;
pub use zstr::*;

mod array_zstring;
pub use array_zstring::*;

#[cfg(feature = "alloc")]
mod _zstring;
#[cfg(feature = "alloc")]
pub use _zstring::*;
