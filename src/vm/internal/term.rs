// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use bincode::{Decode, Encode};
use ibig::ops::Abs;
use ibig::{ibig, ubig, IBig, UBig};
use num_traits::identities::Zero;
use num_traits::ToPrimitive;
use std::{fmt, mem};

const WORD_SIZE: usize = 8; // 8 bytes on 64bit machines
pub const EMPTY_VEC_HEAP_SIZE: usize = 3 * WORD_SIZE; // 3 words

const ZERO_HASH160: [u8; 20] = [0; 20];
const ZERO_HASH256: [u8; 32] = [0; 32];
const ZERO_HASH512: [u8; 64] = [0; 64];

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum VmTerm {
    Hash160([u8; 20]),
    Hash256([u8; 32]),
    Hash512([u8; 64]),
    Unsigned8(u8),
    Unsigned16(u16),
    Unsigned32(u32),
    Unsigned64(u64),
    Unsigned128(u128),
    UnsignedBig(UBig),
    Signed8(i8),
    Signed16(i16),
    Signed32(i32),
    Signed64(i64),
    Signed128(i128),
    SignedBig(IBig),
    Hash160Array(Vec<[u8; 20]>),
    Hash256Array(Vec<[u8; 32]>),
    Hash512Array(Vec<[u8; 64]>),
    Unsigned8Array(Vec<u8>),
    Unsigned16Array(Vec<u16>),
    Unsigned32Array(Vec<u32>),
    Unsigned64Array(Vec<u64>),
    Unsigned128Array(Vec<u128>),
    UnsignedBigArray(Vec<UBig>),
    Signed8Array(Vec<i8>),
    Signed16Array(Vec<i16>),
    Signed32Array(Vec<i32>),
    Signed64Array(Vec<i64>),
    Signed128Array(Vec<i128>),
    SignedBigArray(Vec<IBig>),
}

macro_rules! impl_hash_debug {
    ($f:expr, $val:expr, $struc:expr) => {
        $f.debug_tuple($struc).field(&hex::encode($val)).finish()
    };
}

macro_rules! impl_normal_debug {
    ($f:expr, $val:expr, $struc:expr) => {
        $f.debug_tuple($struc).field(&$val).finish()
    };
}

macro_rules! impl_hash_array_debug {
    ($f:expr, $val:expr, $struc:expr) => {{
        let encoded: Vec<_> = $val.iter().map(|e| hex::encode(e)).collect();
        $f.debug_tuple($struc).field(&encoded).finish()
    }};
}

macro_rules! check_array_values {
    ($arr:expr, $val:expr) => {{
        for v in $arr.iter() {
            if *v != $val {
                return false;
            }
        }
        true
    }};
}

impl fmt::Debug for VmTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Hash160(val) => impl_hash_debug!(f, val, "Hash160"),
            Self::Hash256(val) => impl_hash_debug!(f, val, "Hash256"),
            Self::Hash512(val) => impl_hash_debug!(f, val, "Hash512"),
            Self::Unsigned8(val) => impl_normal_debug!(f, val, "Unsigned8"),
            Self::Unsigned16(val) => impl_normal_debug!(f, val, "Unsigned16"),
            Self::Unsigned32(val) => impl_normal_debug!(f, val, "Unsigned32"),
            Self::Unsigned64(val) => impl_normal_debug!(f, val, "Unsigned64"),
            Self::Unsigned128(val) => impl_normal_debug!(f, val, "Unsigned128"),
            Self::UnsignedBig(val) => impl_normal_debug!(f, val, "UnsignedBig"),
            Self::Signed8(val) => impl_normal_debug!(f, val, "Signed8"),
            Self::Signed16(val) => impl_normal_debug!(f, val, "Signed16"),
            Self::Signed32(val) => impl_normal_debug!(f, val, "Signed32"),
            Self::Signed64(val) => impl_normal_debug!(f, val, "Signed64"),
            Self::Signed128(val) => impl_normal_debug!(f, val, "Signed128"),
            Self::SignedBig(val) => impl_normal_debug!(f, val, "SignedBig"),
            Self::Unsigned8Array(val) => impl_normal_debug!(f, val, "Unsigned8Array"),
            Self::Unsigned16Array(val) => impl_normal_debug!(f, val, "Unsigned16Array"),
            Self::Unsigned32Array(val) => impl_normal_debug!(f, val, "Unsigned32Array"),
            Self::Unsigned64Array(val) => impl_normal_debug!(f, val, "Unsigned64Array"),
            Self::Unsigned128Array(val) => impl_normal_debug!(f, val, "Unsigned128Array"),
            Self::UnsignedBigArray(val) => impl_normal_debug!(f, val, "UnsignedBigArray"),
            Self::Signed8Array(val) => impl_normal_debug!(f, val, "Signed8Array"),
            Self::Signed16Array(val) => impl_normal_debug!(f, val, "Signed16Array"),
            Self::Signed32Array(val) => impl_normal_debug!(f, val, "Signed32Array"),
            Self::Signed64Array(val) => impl_normal_debug!(f, val, "Signed64Array"),
            Self::Signed128Array(val) => impl_normal_debug!(f, val, "Signed128Array"),
            Self::SignedBigArray(val) => impl_normal_debug!(f, val, "SignedBigArray"),
            Self::Hash160Array(val) => impl_hash_array_debug!(f, val, "Hash160Array"),
            Self::Hash256Array(val) => impl_hash_array_debug!(f, val, "Hash256Array"),
            Self::Hash512Array(val) => impl_hash_array_debug!(f, val, "Hash512Array"),
        }
    }
}

impl VmTerm {
    /// Converts the term to a byte vector.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    /// Converts the term to a byte vector without encoding the type.
    #[must_use]
    pub fn to_bytes_raw(&self) -> Vec<u8> {
        match self {
            Self::Hash160(val) => val.to_vec(),
            Self::Hash256(val) => val.to_vec(),
            Self::Hash512(val) => val.to_vec(),
            Self::Unsigned8(val) => val.to_le_bytes().to_vec(),
            Self::Unsigned16(val) => val.to_le_bytes().to_vec(),
            Self::Unsigned32(val) => val.to_le_bytes().to_vec(),
            Self::Unsigned64(val) => val.to_le_bytes().to_vec(),
            Self::Unsigned128(val) => val.to_le_bytes().to_vec(),
            Self::UnsignedBig(val) => val.to_le_bytes(),
            Self::Signed8(val) => val.to_le_bytes().to_vec(),
            Self::Signed16(val) => val.to_le_bytes().to_vec(),
            Self::Signed32(val) => val.to_le_bytes().to_vec(),
            Self::Signed64(val) => val.to_le_bytes().to_vec(),
            Self::Signed128(val) => val.to_le_bytes().to_vec(),
            Self::SignedBig(val) => {
                let sign = val.signum().to_f32() as i8;
                let v = val.abs();

                let num: UBig = v.try_into().unwrap();
                let mut bytes = num.to_le_bytes();
                let mut sign_num = unsafe { mem::transmute::<i8, u8>(sign) };
                bytes.push(sign_num);

                bytes
            }
            Self::Unsigned8Array(val) => val.clone(),
            Self::Unsigned16Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Unsigned32Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Unsigned64Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Unsigned128Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::UnsignedBigArray(val) => val.iter().flat_map(ibig::UBig::to_le_bytes).collect(),
            Self::Signed8Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Signed16Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Signed32Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Signed64Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::Signed128Array(val) => val.iter().flat_map(|v| v.to_le_bytes()).collect(),
            Self::SignedBigArray(val) => val
                .iter()
                .flat_map(|v| {
                    let sign = v.signum().to_f32() as i8;
                    let v = v.abs();

                    let num: UBig = v.try_into().unwrap();
                    let mut bytes = num.to_le_bytes();
                    let sign_num = unsafe { mem::transmute::<i8, u8>(sign) };
                    bytes.push(sign_num);

                    bytes
                })
                .collect(),
            Self::Hash160Array(val) => val.iter().flat_map(|v| v.to_vec()).collect(),
            Self::Hash256Array(val) => val.iter().flat_map(|v| v.to_vec()).collect(),
            Self::Hash512Array(val) => val.iter().flat_map(|v| v.to_vec()).collect(),
        }
    }

    pub fn add_one(&mut self) -> Option<()> {
        match self {
            Self::Unsigned8(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Unsigned16(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Unsigned32(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Unsigned64(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Unsigned128(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::UnsignedBig(ref mut val) => {
                *val += 1;
            }
            Self::Signed8(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Signed16(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Signed32(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Signed64(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::Signed128(ref mut val) => {
                *val = val.checked_add(1)?;
            }
            Self::SignedBig(ref mut val) => {
                *val += 1;
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn add(&mut self, rhs: &VmTerm) -> Option<()> {
        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val += rhs_val;
            }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val = lhs_val.checked_add(*rhs_val)?;
            }
            (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val += rhs_val;
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
                lhs_val.extend_from_slice(rhs_val);
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn sub_one(&mut self) -> Option<()> {
        match self {
            Self::Unsigned8(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Unsigned16(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Unsigned32(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Unsigned64(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Unsigned128(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::UnsignedBig(ref mut val) => {
                *val -= 1;
            }
            Self::Signed8(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Signed16(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Signed32(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Signed64(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::Signed128(ref mut val) => {
                *val = val.checked_sub(1)?;
            }
            Self::SignedBig(ref mut val) => {
                *val -= 1;
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn sub(&mut self, rhs: &VmTerm) -> Option<()> {
        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val -= rhs_val;
            }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val = lhs_val.checked_sub(*rhs_val)?;
            }
            (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val -= rhs_val;
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x - rhs_val).collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for val in &mut *lhs_val {
                    *val = val.checked_sub(*rhs_val)?;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x - rhs_val).collect();
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x - y)
                    .collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_sub(*y)?;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x - y)
                    .collect();
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn mul(&mut self, rhs: &VmTerm) -> Option<()> {
        if self.is_array() && rhs.is_array() && self.size() != rhs.size() {
            return None;
        }

        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val *= rhs_val;
            }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val = lhs_val.checked_mul(*rhs_val)?;
            }
            (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val *= rhs_val;
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x * rhs_val).collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_mul(*rhs_val)?;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x * rhs_val).collect();
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x * y)
                    .collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_mul(*y)?;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x * y)
                    .collect();
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn div(&mut self, rhs: &VmTerm) -> Option<()> {
        if self.is_array() && rhs.is_array() && self.size() != rhs.size() {
            return None;
        }

        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val /= rhs_val;
            }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val = lhs_val.checked_div(*rhs_val)?;
            }
            (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val /= rhs_val;
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x / rhs_val).collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x = x.checked_div(*rhs_val)?;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x / rhs_val).collect();
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x / y)
                    .collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x = x.checked_div(*y)?;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x / y)
                    .collect();
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    /// Returns the virtual heap size of the term in bytes
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            Self::Hash160(_) => 20,
            Self::Hash256(_) => 32,
            Self::Hash512(_) => 64,
            Self::Unsigned8(_) | Self::Signed8(_) => 1,
            Self::Unsigned16(_) | Self::Signed16(_) => 2,
            Self::Unsigned32(_) | Self::Signed32(_) => 4,
            Self::Unsigned64(_) | Self::Signed64(_) => 8,
            Self::Unsigned128(_) | Self::Signed128(_) => 16,
            Self::UnsignedBig(v) => {
                (v.bit_len() >> 3) + EMPTY_VEC_HEAP_SIZE // additional vec allocated by ubig
            }
            Self::SignedBig(v) => {
                let v = v.abs();
                let v: UBig = v.try_into().unwrap();
                (v.bit_len() >> 3) + EMPTY_VEC_HEAP_SIZE + WORD_SIZE // additional vec allocated by ibig plus sign
            }
            Self::Hash160Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 20,
            Self::Hash256Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 32,
            Self::Hash512Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 64,
            Self::Unsigned8Array(val) => EMPTY_VEC_HEAP_SIZE + val.len(),
            Self::Signed8Array(val) => EMPTY_VEC_HEAP_SIZE + val.len(),
            Self::Unsigned16Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 2,
            Self::Signed16Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 2,
            Self::Unsigned32Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 4,
            Self::Signed32Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 4,
            Self::Unsigned64Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 8,
            Self::Signed64Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 8,
            Self::Unsigned128Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 16,
            Self::Signed128Array(val) => EMPTY_VEC_HEAP_SIZE + val.len() * 16,
            Self::UnsignedBigArray(val) => {
                let mut size = EMPTY_VEC_HEAP_SIZE;
                for v in val {
                    size += (v.bit_len() >> 3) + EMPTY_VEC_HEAP_SIZE; // additional vec allocated by ubig
                }
                size
            }
            Self::SignedBigArray(val) => {
                let mut size = EMPTY_VEC_HEAP_SIZE;
                for v in val {
                    let v = v.abs();
                    let v: UBig = v.try_into().unwrap();
                    size += (v.bit_len() >> 3) + EMPTY_VEC_HEAP_SIZE + WORD_SIZE;
                    // additional vec allocated by ibig plus sign
                }
                size
            }
        }
    }

    /// Returns the type of the term
    #[must_use]
    pub fn get_type(&self) -> u8 {
        match self {
            Self::Hash160(_) => 0x00_u8,
            Self::Hash256(_) => 0x01_u8,
            Self::Hash512(_) => 0x02_u8,
            Self::Unsigned8(_) => 0x03_u8,
            Self::Unsigned16(_) => 0x04_u8,
            Self::Unsigned32(_) => 0x05_u8,
            Self::Unsigned64(_) => 0x06_u8,
            Self::Unsigned128(_) => 0x07_u8,
            Self::UnsignedBig(_) => 0x08_u8,
            Self::Signed8(_) => 0x09_u8,
            Self::Signed16(_) => 0x0a_u8,
            Self::Signed32(_) => 0x0b_u8,
            Self::Signed64(_) => 0x0c_u8,
            Self::Signed128(_) => 0x0d_u8,
            Self::SignedBig(_) => 0x0e_u8,
            Self::Hash160Array(_) => 0x0f_u8,
            Self::Hash256Array(_) => 0x10_u8,
            Self::Hash512Array(_) => 0x11_u8,
            Self::Unsigned8Array(_) => 0x12_u8,
            Self::Unsigned16Array(_) => 0x13_u8,
            Self::Unsigned32Array(_) => 0x14_u8,
            Self::Unsigned64Array(_) => 0x15_u8,
            Self::Unsigned128Array(_) => 0x16_u8,
            Self::UnsignedBigArray(_) => 0x17_u8,
            Self::Signed8Array(_) => 0x18_u8,
            Self::Signed16Array(_) => 0x19_u8,
            Self::Signed32Array(_) => 0x1a_u8,
            Self::Signed64Array(_) => 0x1b_u8,
            Self::Signed128Array(_) => 0x1c_u8,
            Self::SignedBigArray(_) => 0x1d_u8,
        }
    }

    /// Checks if the value of the term equals to 0
    #[must_use]
    pub fn equals_0(&self) -> bool {
        match self {
            Self::Hash160(val) => *val == ZERO_HASH160,
            Self::Hash256(val) => *val == ZERO_HASH256,
            Self::Hash512(val) => *val == ZERO_HASH512,
            Self::Unsigned8(val) => *val == 0_u8,
            Self::Unsigned16(val) => *val == 0_u16,
            Self::Unsigned32(val) => *val == 0_u32,
            Self::Unsigned64(val) => *val == 0_u64,
            Self::Unsigned128(val) => *val == 0_u128,
            Self::UnsignedBig(val) => *val == ubig!(0),
            Self::Signed8(val) => *val == 0_i8,
            Self::Signed16(val) => *val == 0_i16,
            Self::Signed32(val) => *val == 0_i32,
            Self::Signed64(val) => *val == 0_i64,
            Self::Signed128(val) => *val == 0_i128,
            Self::SignedBig(val) => *val == ibig!(0),
            Self::Hash160Array(val) => check_array_values!(*val, ZERO_HASH160),
            Self::Hash256Array(val) => check_array_values!(*val, ZERO_HASH256),
            Self::Hash512Array(val) => check_array_values!(*val, ZERO_HASH512),
            Self::Unsigned8Array(val) => check_array_values!(*val, 0_u8),
            Self::Unsigned16Array(val) => check_array_values!(*val, 0_u16),
            Self::Unsigned32Array(val) => check_array_values!(*val, 0_u32),
            Self::Unsigned64Array(val) => check_array_values!(*val, 0_u64),
            Self::Unsigned128Array(val) => check_array_values!(*val, 0_u128),
            Self::UnsignedBigArray(val) => check_array_values!(*val, ubig!(0)),
            Self::Signed8Array(val) => check_array_values!(*val, 0_i8),
            Self::Signed16Array(val) => check_array_values!(*val, 0_i16),
            Self::Signed32Array(val) => check_array_values!(*val, 0_i32),
            Self::Signed64Array(val) => check_array_values!(*val, 0_i64),
            Self::Signed128Array(val) => check_array_values!(*val, 0_i128),
            Self::SignedBigArray(val) => check_array_values!(*val, ibig!(0)),
        }
    }

    /// Checks if the value of the term equals to 1
    #[must_use]
    pub fn equals_1(&self) -> bool {
        match self {
            Self::Hash160(val) => {
                let mut arr: [u8; 20] = [0; 20];
                arr[0] = 0x01;
                *val == arr
            }
            Self::Hash256(val) => {
                let mut arr: [u8; 32] = [0; 32];
                arr[0] = 0x01;
                *val == arr
            }
            Self::Hash512(val) => {
                let mut arr: [u8; 64] = [0; 64];
                arr[0] = 0x01;
                *val == arr
            }
            Self::Unsigned8(val) => *val == 1_u8,
            Self::Unsigned16(val) => *val == 1_u16,
            Self::Unsigned32(val) => *val == 1_u32,
            Self::Unsigned64(val) => *val == 1_u64,
            Self::Unsigned128(val) => *val == 1_u128,
            Self::UnsignedBig(val) => *val == ubig!(1),
            Self::Signed8(val) => *val == 1_i8,
            Self::Signed16(val) => *val == 1_i16,
            Self::Signed32(val) => *val == 1_i32,
            Self::Signed64(val) => *val == 1_i64,
            Self::Signed128(val) => *val == 1_i128,
            Self::SignedBig(val) => *val == ibig!(1),
            Self::Hash160Array(val) => {
                let mut arr: [u8; 20] = [0; 20];
                arr[0] = 0x01;
                check_array_values!(*val, arr)
            }
            Self::Hash256Array(val) => {
                let mut arr: [u8; 32] = [0; 32];
                arr[0] = 0x01;
                check_array_values!(*val, arr)
            }
            Self::Hash512Array(val) => {
                let mut arr: [u8; 64] = [0; 64];
                arr[0] = 0x01;
                check_array_values!(*val, arr)
            }
            Self::Unsigned8Array(val) => check_array_values!(*val, 1_u8),
            Self::Unsigned16Array(val) => check_array_values!(*val, 1_u16),
            Self::Unsigned32Array(val) => check_array_values!(*val, 1_u32),
            Self::Unsigned64Array(val) => check_array_values!(*val, 1_u64),
            Self::Unsigned128Array(val) => check_array_values!(*val, 1_u128),
            Self::UnsignedBigArray(val) => check_array_values!(*val, ubig!(1)),
            Self::Signed8Array(val) => check_array_values!(*val, 1_i8),
            Self::Signed16Array(val) => check_array_values!(*val, 1_i16),
            Self::Signed32Array(val) => check_array_values!(*val, 1_i32),
            Self::Signed64Array(val) => check_array_values!(*val, 1_i64),
            Self::Signed128Array(val) => check_array_values!(*val, 1_i128),
            Self::SignedBigArray(val) => check_array_values!(*val, ibig!(1)),
        }
    }

    /// Checks if the two terms are comparable
    #[must_use]
    pub fn is_comparable(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Hash160(_), Self::Hash160(_)) => true,
            (Self::Hash256(_), Self::Hash256(_)) => true,
            (Self::Hash512(_), Self::Hash512(_)) => true,
            (Self::Unsigned8(_), Self::Unsigned8(_)) => true,
            (Self::Unsigned16(_), Self::Unsigned16(_)) => true,
            (Self::Unsigned32(_), Self::Unsigned32(_)) => true,
            (Self::Unsigned64(_), Self::Unsigned64(_)) => true,
            (Self::Unsigned128(_), Self::Unsigned128(_)) => true,
            (Self::UnsignedBig(_), Self::UnsignedBig(_)) => true,
            (Self::Signed8(_), Self::Signed8(_)) => true,
            (Self::Signed16(_), Self::Signed16(_)) => true,
            (Self::Signed32(_), Self::Signed32(_)) => true,
            (Self::Signed64(_), Self::Signed64(_)) => true,
            (Self::Signed128(_), Self::Signed128(_)) => true,
            (Self::SignedBig(_), Self::SignedBig(_)) => true,
            (Self::Hash160Array(arr1), Self::Hash160Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Hash256Array(arr1), Self::Hash256Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Hash512Array(arr1), Self::Hash512Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Unsigned8Array(arr1), Self::Unsigned8Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Unsigned16Array(arr1), Self::Unsigned16Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Unsigned32Array(arr1), Self::Unsigned32Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Unsigned64Array(arr1), Self::Unsigned64Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Unsigned128Array(arr1), Self::Unsigned128Array(arr2)) => {
                arr1.len() == arr2.len()
            }
            (Self::UnsignedBigArray(arr1), Self::UnsignedBigArray(arr2)) => {
                arr1.len() == arr2.len()
            }
            (Self::Signed8Array(arr1), Self::Signed8Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Signed16Array(arr1), Self::Signed16Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Signed32Array(arr1), Self::Signed32Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Signed64Array(arr1), Self::Signed64Array(arr2)) => arr1.len() == arr2.len(),
            (Self::Signed128Array(arr1), Self::Signed128Array(arr2)) => arr1.len() == arr2.len(),
            (Self::SignedBigArray(arr1), Self::SignedBigArray(arr2)) => arr1.len() == arr2.len(),
            _ => false,
        }
    }

    /// Checks if the term is an array type
    #[must_use]
    pub fn is_array(&self) -> bool {
        match self {
            Self::Hash160(_) => false,
            Self::Hash256(_) => false,
            Self::Hash512(_) => false,
            Self::Unsigned8(_) => false,
            Self::Unsigned16(_) => false,
            Self::Unsigned32(_) => false,
            Self::Unsigned64(_) => false,
            Self::Unsigned128(_) => false,
            Self::UnsignedBig(_) => false,
            Self::Signed8(_) => false,
            Self::Signed16(_) => false,
            Self::Signed32(_) => false,
            Self::Signed64(_) => false,
            Self::Signed128(_) => false,
            Self::SignedBig(_) => false,
            Self::Hash160Array(_) => true,
            Self::Hash256Array(_) => true,
            Self::Hash512Array(_) => true,
            Self::Unsigned8Array(_) => true,
            Self::Unsigned16Array(_) => true,
            Self::Unsigned32Array(_) => true,
            Self::Unsigned64Array(_) => true,
            Self::Unsigned128Array(_) => true,
            Self::UnsignedBigArray(_) => true,
            Self::Signed8Array(_) => true,
            Self::Signed16Array(_) => true,
            Self::Signed32Array(_) => true,
            Self::Signed64Array(_) => true,
            Self::Signed128Array(_) => true,
            Self::SignedBigArray(_) => true,
        }
    }

    /// Returns the length if the `VmTerm` is an array type, 0 otherwise
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Self::Hash160Array(arr) => arr.len(),
            Self::Hash256Array(arr) => arr.len(),
            Self::Hash512Array(arr) => arr.len(),
            Self::Unsigned8Array(arr) => arr.len(),
            Self::Unsigned16Array(arr) => arr.len(),
            Self::Unsigned32Array(arr) => arr.len(),
            Self::Unsigned64Array(arr) => arr.len(),
            Self::Unsigned128Array(arr) => arr.len(),
            Self::UnsignedBigArray(arr) => arr.len(),
            Self::Signed8Array(arr) => arr.len(),
            Self::Signed16Array(arr) => arr.len(),
            Self::Signed32Array(arr) => arr.len(),
            Self::Signed64Array(arr) => arr.len(),
            Self::Signed128Array(arr) => arr.len(),
            Self::SignedBigArray(arr) => arr.len(),
            _ => 0,
        }
    }

    /// Divides a vector into two at a specified index, without bounds checks
    #[must_use]
    pub fn split_at_unchecked(&self, mid: usize) -> Option<(VmTerm, VmTerm)> {
        match self {
            Self::Hash160Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Hash160Array(left.to_vec()),
                    VmTerm::Hash160Array(right.to_vec()),
                ))
            },
            Self::Hash256Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Hash256Array(left.to_vec()),
                    VmTerm::Hash256Array(right.to_vec()),
                ))
            },
            Self::Hash512Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Hash512Array(left.to_vec()),
                    VmTerm::Hash512Array(right.to_vec()),
                ))
            },
            Self::Unsigned8Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Unsigned8Array(left.to_vec()),
                    VmTerm::Unsigned8Array(right.to_vec()),
                ))
            },
            Self::Unsigned16Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Unsigned16Array(left.to_vec()),
                    VmTerm::Unsigned16Array(right.to_vec()),
                ))
            },
            Self::Unsigned32Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Unsigned32Array(left.to_vec()),
                    VmTerm::Unsigned32Array(right.to_vec()),
                ))
            },
            Self::Unsigned64Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Unsigned64Array(left.to_vec()),
                    VmTerm::Unsigned64Array(right.to_vec()),
                ))
            },
            Self::Unsigned128Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Unsigned128Array(left.to_vec()),
                    VmTerm::Unsigned128Array(right.to_vec()),
                ))
            },
            Self::UnsignedBigArray(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::UnsignedBigArray(left.to_vec()),
                    VmTerm::UnsignedBigArray(right.to_vec()),
                ))
            },
            Self::Signed8Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Signed8Array(left.to_vec()),
                    VmTerm::Signed8Array(right.to_vec()),
                ))
            },
            Self::Signed16Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Signed16Array(left.to_vec()),
                    VmTerm::Signed16Array(right.to_vec()),
                ))
            },
            Self::Signed32Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Signed32Array(left.to_vec()),
                    VmTerm::Signed32Array(right.to_vec()),
                ))
            },
            Self::Signed64Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Signed64Array(left.to_vec()),
                    VmTerm::Signed64Array(right.to_vec()),
                ))
            },
            Self::Signed128Array(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::Signed128Array(left.to_vec()),
                    VmTerm::Signed128Array(right.to_vec()),
                ))
            },
            Self::SignedBigArray(arr) => unsafe {
                let (left, right) = arr.split_at_unchecked(mid);
                Some((
                    VmTerm::SignedBigArray(left.to_vec()),
                    VmTerm::SignedBigArray(right.to_vec()),
                ))
            },
            _ => None,
        }
    }

    pub fn not(&mut self) -> Option<()> {
        // TODO: add for ibig, ubig
        match self {
            Self::Unsigned8(ref mut val) => {
                *val = !*val;
            }
            Self::Unsigned16(ref mut val) => {
                *val = !*val;
            }
            Self::Unsigned32(ref mut val) => {
                *val = !*val;
            }
            Self::Unsigned64(ref mut val) => {
                *val = !*val;
            }
            Self::Unsigned128(ref mut val) => {
                *val = !*val;
            }
            Self::Signed8(ref mut val) => {
                *val = !*val;
            }
            Self::Signed16(ref mut val) => {
                *val = !*val;
            }
            Self::Signed32(ref mut val) => {
                *val = !*val;
            }
            Self::Signed64(ref mut val) => {
                *val = !*val;
            }
            Self::Signed128(ref mut val) => {
                *val = !*val;
            }
            Self::Unsigned8Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Unsigned16Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Unsigned32Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Unsigned64Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Unsigned128Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Signed8Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Signed16Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Signed32Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Signed64Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            Self::Signed128Array(ref mut val) => {
                for x in &mut *val {
                    *x = !*x;
                }
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn or(&mut self, rhs: &VmTerm) -> Option<()> {
        if self.is_array() && rhs.is_array() && self.size() != rhs.size() {
            return None;
        }

        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val |= rhs_val;
            }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val |= *rhs_val;
            }
            (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val |= rhs_val;
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x | rhs_val).collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x |= *rhs_val;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x | rhs_val).collect();
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x | y)
                    .collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x |= *y;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x | y)
                    .collect();
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn xor(&mut self, rhs: &VmTerm) -> Option<()> {
        if self.is_array() && rhs.is_array() && self.size() != rhs.size() {
            return None;
        }

        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val ^= rhs_val;
            }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val ^= *rhs_val;
            }
            (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val ^= rhs_val;
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x ^ rhs_val).collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x ^= *rhs_val;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
                *lhs_val = lhs_val.iter().map(|x| x ^ rhs_val).collect();
            }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x ^ y)
                    .collect();
            }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x ^= *y;
                }
            }
            (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
                *lhs_val = lhs_val
                    .iter()
                    .zip(rhs_val.iter())
                    .map(|(x, y)| x ^ y)
                    .collect();
            }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn sh_left(&mut self, rhs: &VmTerm) -> Option<()> {
        // TODO: add for ibig, ubig
        if self.is_array() && rhs.is_array() && self.size() != rhs.size() {
            return None;
        }

        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            // (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
            //     *lhs_val <<= rhs_val;
            // }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val <<= *rhs_val;
            }
            // (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
            //     *lhs_val <<= rhs_val;
            // }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            // (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
            //     *lhs_val = lhs_val.iter().map(|x| x << rhs_val).collect();
            // }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x <<= *rhs_val;
                }
            }
            // (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
            //     *lhs_val = lhs_val.iter().map(|x| x << rhs_val).collect();
            // }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            // (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
            //     *lhs_val = lhs_val
            //         .iter()
            //         .zip(rhs_val.iter())
            //         .map(|(x, y)| x << y)
            //         .collect();
            // }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x <<= *y;
                }
            }
            // (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
            //     *lhs_val = lhs_val
            //         .iter()
            //         .zip(rhs_val.iter())
            //         .map(|(x, y)| x << y)
            //         .collect();
            // }
            _ => {
                return None;
            }
        }

        Some(())
    }

    pub fn sh_right(&mut self, rhs: &VmTerm) -> Option<()> {
        // TODO: add for ibig, ubig
        if self.is_array() && rhs.is_array() && self.size() != rhs.size() {
            return None;
        }

        match (self, rhs) {
            (Self::Unsigned8(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Unsigned16(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Unsigned32(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Unsigned64(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Unsigned128(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            // (Self::UnsignedBig(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
            //     *lhs_val >>= rhs_val;
            // }
            (Self::Signed8(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Signed16(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Signed32(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Signed64(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            (Self::Signed128(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                *lhs_val >>= *rhs_val;
            }
            // (Self::SignedBig(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
            //     *lhs_val >>= rhs_val;
            // }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            // (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBig(rhs_val)) => {
            //     *lhs_val = lhs_val.iter().map(|x| x >> rhs_val).collect();
            // }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128(rhs_val)) => {
                for x in &mut *lhs_val {
                    *x >>= *rhs_val;
                }
            }
            // (Self::SignedBigArray(ref mut lhs_val), Self::SignedBig(rhs_val)) => {
            //     *lhs_val = lhs_val.iter().map(|x| x >> rhs_val).collect();
            // }
            (Self::Unsigned8Array(ref mut lhs_val), Self::Unsigned8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Unsigned16Array(ref mut lhs_val), Self::Unsigned16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Unsigned32Array(ref mut lhs_val), Self::Unsigned32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Unsigned64Array(ref mut lhs_val), Self::Unsigned64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Unsigned128Array(ref mut lhs_val), Self::Unsigned128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            // (Self::UnsignedBigArray(ref mut lhs_val), Self::UnsignedBigArray(rhs_val)) => {
            //     *lhs_val = lhs_val
            //         .iter()
            //         .zip(rhs_val.iter())
            //         .map(|(x, y)| x >> y)
            //         .collect();
            // }
            (Self::Signed8Array(ref mut lhs_val), Self::Signed8Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Signed16Array(ref mut lhs_val), Self::Signed16Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Signed32Array(ref mut lhs_val), Self::Signed32Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Signed64Array(ref mut lhs_val), Self::Signed64Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            (Self::Signed128Array(ref mut lhs_val), Self::Signed128Array(rhs_val)) => {
                for (x, y) in lhs_val.iter_mut().zip(rhs_val.iter()) {
                    *x >>= *y;
                }
            }
            // (Self::SignedBigArray(ref mut lhs_val), Self::SignedBigArray(rhs_val)) => {
            //     *lhs_val = lhs_val
            //         .iter()
            //         .zip(rhs_val.iter())
            //         .map(|(x, y)| x >> y)
            //         .collect();
            // }
            _ => {
                return None;
            }
        }

        Some(())
    }
}

impl Encode for VmTerm {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        match self {
            Self::Hash160(ref v) => {
                bincode::Encode::encode(&0x00_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Hash256(ref v) => {
                bincode::Encode::encode(&0x01_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Hash512(ref v) => {
                bincode::Encode::encode(&0x02_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Unsigned8(ref v) => {
                bincode::Encode::encode(&0x03_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Unsigned16(ref v) => {
                bincode::Encode::encode(&0x04_u8, encoder)?;
                let v: [u8; 2] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::Unsigned32(ref v) => {
                bincode::Encode::encode(&0x05_u8, encoder)?;
                let v: [u8; 4] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::Unsigned64(ref v) => {
                bincode::Encode::encode(&0x06_u8, encoder)?;
                let v: [u8; 8] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::Unsigned128(ref v) => {
                bincode::Encode::encode(&0x07_u8, encoder)?;
                let v: [u8; 16] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::UnsignedBig(ref v) => {
                let bytes = v.to_le_bytes();
                bincode::Encode::encode(&0x08_u8, encoder)?;
                bincode::Encode::encode(&bytes, encoder)?;
            }

            Self::Signed8(ref v) => {
                bincode::Encode::encode(&0x09_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Signed16(ref v) => {
                bincode::Encode::encode(&0x0a_u8, encoder)?;
                let v: [u8; 2] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::Signed32(ref v) => {
                bincode::Encode::encode(&0x0b_u8, encoder)?;
                let v: [u8; 4] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::Signed64(ref v) => {
                bincode::Encode::encode(&0x0c_u8, encoder)?;
                let v: [u8; 8] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::Signed128(ref v) => {
                bincode::Encode::encode(&0x0d_u8, encoder)?;
                let v: [u8; 16] = v.to_le_bytes();
                bincode::Encode::encode(&v, encoder)?;
            }

            Self::SignedBig(ref v) => {
                let sign = v.signum().to_f32() as i8;
                let v = v.abs();

                match sign {
                    -1 => {
                        bincode::Encode::encode(&0x0e_u8, encoder)?;
                        let v: UBig = v.try_into().unwrap();
                        let bytes = v.to_le_bytes();
                        bincode::Encode::encode(&bytes, encoder)?;
                    }

                    1 => {
                        bincode::Encode::encode(&0x0f_u8, encoder)?;
                        let v: UBig = v.try_into().unwrap();
                        let bytes = v.to_le_bytes();
                        bincode::Encode::encode(&bytes, encoder)?;
                    }

                    0 => {
                        bincode::Encode::encode(&0x10_u8, encoder)?;
                    }

                    _ => unreachable!(),
                }
            }

            Self::Hash160Array(ref v) => {
                bincode::Encode::encode(&0x13_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Hash256Array(ref v) => {
                bincode::Encode::encode(&0x14_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Hash512Array(ref v) => {
                bincode::Encode::encode(&0x15_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Unsigned8Array(ref v) => {
                bincode::Encode::encode(&0x16_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Unsigned16Array(ref v) => {
                bincode::Encode::encode(&0x17_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 2);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Unsigned32Array(ref v) => {
                bincode::Encode::encode(&0x18_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 4);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Unsigned64Array(ref v) => {
                bincode::Encode::encode(&0x19_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 8);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Unsigned128Array(ref v) => {
                bincode::Encode::encode(&0x1a_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 16);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::UnsignedBigArray(ref v) => {
                bincode::Encode::encode(&0x1b_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 32);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Signed8Array(ref v) => {
                bincode::Encode::encode(&0x1c_u8, encoder)?;
                bincode::Encode::encode(v, encoder)?;
            }

            Self::Signed16Array(ref v) => {
                bincode::Encode::encode(&0x1d_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 2);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Signed32Array(ref v) => {
                bincode::Encode::encode(&0x1e_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 4);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Signed64Array(ref v) => {
                bincode::Encode::encode(&0x1f_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 8);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::Signed128Array(ref v) => {
                bincode::Encode::encode(&0x20_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * 16);
                for v in v {
                    buf.extend_from_slice(&v.to_le_bytes());
                }
                bincode::Encode::encode(&buf, encoder)?;
            }

            Self::SignedBigArray(ref v) => {
                bincode::Encode::encode(&0x21_u8, encoder)?;
                let mut buf = Vec::with_capacity(v.len() * (32 + 1));
                for v in v {
                    let sign = v.signum().to_f32() as i8;
                    let v = v.abs();

                    match sign {
                        -1 => {
                            buf.extend_from_slice(&[0x0e_u8]);
                            let v: UBig = v.try_into().unwrap();
                            let bytes = v.to_le_bytes();
                            buf.extend_from_slice(&bytes);
                        }

                        1 => {
                            buf.extend_from_slice(&[0x0f_u8]);
                            let v: UBig = v.try_into().unwrap();
                            let bytes = v.to_le_bytes();
                            buf.extend_from_slice(&bytes);
                        }

                        0 => {
                            buf.extend_from_slice(&[0x10_u8]);
                        }

                        _ => unreachable!(),
                    }
                }
                bincode::Encode::encode(&buf, encoder)?;
            }
        }

        Ok(())
    }
}

impl Decode for VmTerm {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let t: u8 = bincode::Decode::decode(decoder)?;

        match t {
            0x00 => {
                let v: [u8; 20] = bincode::Decode::decode(decoder)?;
                Ok(VmTerm::Hash160(v))
            }

            0x01 => {
                let v: [u8; 32] = bincode::Decode::decode(decoder)?;
                Ok(VmTerm::Hash256(v))
            }

            0x02 => {
                let v: [u8; 64] = bincode::Decode::decode(decoder)?;
                Ok(VmTerm::Hash512(v))
            }

            0x03 => {
                let v: u8 = bincode::Decode::decode(decoder)?;
                Ok(VmTerm::Unsigned8(v))
            }

            0x04 => {
                let v: [u8; 2] = bincode::Decode::decode(decoder)?;
                let v = u16::from_le_bytes(v);
                Ok(VmTerm::Unsigned16(v))
            }

            0x05 => {
                let v: [u8; 4] = bincode::Decode::decode(decoder)?;
                let v = u32::from_le_bytes(v);
                Ok(VmTerm::Unsigned32(v))
            }

            0x06 => {
                let v: [u8; 8] = bincode::Decode::decode(decoder)?;
                let v = u64::from_le_bytes(v);
                Ok(VmTerm::Unsigned64(v))
            }

            0x07 => {
                let v: [u8; 16] = bincode::Decode::decode(decoder)?;
                let v = u128::from_le_bytes(v);
                Ok(VmTerm::Unsigned128(v))
            }

            0x08 => {
                let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                let v = UBig::from_le_bytes(&v);
                Ok(VmTerm::UnsignedBig(v))
            }

            0x09 => {
                let v: i8 = bincode::Decode::decode(decoder)?;
                Ok(VmTerm::Signed8(v))
            }

            0x0a => {
                let v: [u8; 2] = bincode::Decode::decode(decoder)?;
                let v = i16::from_le_bytes(v);
                Ok(VmTerm::Signed16(v))
            }

            0x0b => {
                let v: [u8; 4] = bincode::Decode::decode(decoder)?;
                let v = i32::from_le_bytes(v);
                Ok(VmTerm::Signed32(v))
            }

            0x0c => {
                let v: [u8; 8] = bincode::Decode::decode(decoder)?;
                let v = i64::from_le_bytes(v);
                Ok(VmTerm::Signed64(v))
            }

            0x0d => {
                let v: [u8; 16] = bincode::Decode::decode(decoder)?;
                let v = i128::from_le_bytes(v);
                Ok(VmTerm::Signed128(v))
            }

            0x0e => {
                let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                let u = UBig::from_le_bytes(&v);
                let i: IBig = u.try_into().map_err(|_| {
                    bincode::error::DecodeError::OtherString("could not parse i256".to_owned())
                })?;
                Ok(VmTerm::SignedBig(i * ibig!(-1)))
            }

            0x0f => {
                let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                let u = UBig::from_le_bytes(&v);
                let i: IBig = u.try_into().map_err(|_| {
                    bincode::error::DecodeError::OtherString("could not parse i256".to_owned())
                })?;
                Ok(VmTerm::SignedBig(i))
            }

            0x10 => Ok(VmTerm::SignedBig(IBig::zero())),

            _ => Err(bincode::error::DecodeError::OtherString(
                "invalid term type".to_owned(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ibig::{ibig, ubig};

    #[test]
    fn test_hash160_encode_decode() {
        let t = VmTerm::Hash160([0xff; 20]);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x00]);
        assert_eq!(encoded.len(), 21);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_hash256_encode_decode() {
        let t = VmTerm::Hash256([0xff; 32]);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x01]);
        assert_eq!(encoded.len(), 33);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_hash512_encode_decode() {
        let t = VmTerm::Hash512([0xff; 64]);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x02]);
        assert_eq!(encoded.len(), 65);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_u8_encode_decode() {
        let t = VmTerm::Unsigned8(12);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x03]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_u16_encode_decode() {
        let t = VmTerm::Unsigned16(12324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x04]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_u32_encode_decode() {
        let t = VmTerm::Unsigned32(1_254_324_324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x05]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_u64_encode_decode() {
        let t = VmTerm::Unsigned64(143_254_324_324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x06]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_u128_encode_decode() {
        let t = VmTerm::Unsigned128(143_254_354_354_324_324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x07]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_u256_encode_decode() {
        let i = ubig!(42432);
        let t = VmTerm::UnsignedBig(i);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x08]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i8_encode_decode_negative() {
        let t = VmTerm::Signed8(-14);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x09]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i8_encode_decode_positive() {
        let t = VmTerm::Signed8(12);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x09]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i16_encode_decode_negative() {
        let t = VmTerm::Signed16(-14423);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0a]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i16_encode_decode_positive() {
        let t = VmTerm::Signed16(12324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0a]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i32_encode_decode_negative() {
        let t = VmTerm::Signed32(-1_432_543_423);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0b]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i32_encode_decode_positive() {
        let t = VmTerm::Signed32(1_254_324_324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0b]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i64_encode_decode_negative() {
        let t = VmTerm::Signed64(-143_254_423_423);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0c]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i64_encode_decode_positive() {
        let t = VmTerm::Signed64(143_254_324_324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0c]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i128_encode_decode_negative() {
        let t = VmTerm::Signed128(-143_254_432_432_423_423_423);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0d]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i128_encode_decode_positive() {
        let t = VmTerm::Signed128(143_254_324_324);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0d]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i256_encode_decode_negative() {
        let i = ibig!(-42432);
        let t = VmTerm::SignedBig(i);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0e]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i256_encode_decode_positive() {
        let i = ibig!(42432);
        let t = VmTerm::SignedBig(i);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded[..1], &[0x0f]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_i256_encode_decode_zero() {
        let i = ibig!(0);
        let t = VmTerm::SignedBig(i);
        let encoded = crate::codec::encode_to_vec(&t).unwrap();
        assert_eq!(&encoded, &[0x10]);
        assert_eq!(crate::codec::decode::<VmTerm>(&encoded).unwrap(), t);
    }

    #[test]
    fn test_equals_0() {
        assert!(VmTerm::Hash160([0; 20]).equals_0());
        assert!(VmTerm::Hash256([0; 32]).equals_0());
        assert!(VmTerm::Hash512([0; 64]).equals_0());
        assert!(VmTerm::Unsigned8(0).equals_0());
        assert!(VmTerm::Unsigned16(0).equals_0());
        assert!(VmTerm::Unsigned32(0).equals_0());
        assert!(VmTerm::Unsigned64(0).equals_0());
        assert!(VmTerm::Unsigned128(0).equals_0());
        assert!(VmTerm::UnsignedBig(ubig!(0)).equals_0());
        assert!(VmTerm::Signed8(0).equals_0());
        assert!(VmTerm::Signed16(0).equals_0());
        assert!(VmTerm::Signed32(0).equals_0());
        assert!(VmTerm::Signed64(0).equals_0());
        assert!(VmTerm::Signed128(0).equals_0());
        assert!(VmTerm::SignedBig(ibig!(0)).equals_0());
        assert!(VmTerm::Hash160Array(vec![[0; 20], [0; 20], [0; 20]]).equals_0());
        assert!(VmTerm::Hash256Array(vec![[0; 32], [0; 32], [0; 32], [0; 32]]).equals_0());
        assert!(VmTerm::Hash512Array(vec![[0; 64], [0; 64], [0; 64], [0; 64], [0; 64]]).equals_0());
        assert!(VmTerm::Unsigned8Array(vec![0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Unsigned16Array(vec![0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Unsigned32Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Unsigned64Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Unsigned128Array(vec![0, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::UnsignedBigArray(vec![ubig!(0), ubig!(0), ubig!(0)]).equals_0());
        assert!(VmTerm::Signed8Array(vec![0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Signed16Array(vec![0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Signed32Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Signed64Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::Signed128Array(vec![0, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(VmTerm::SignedBigArray(vec![ibig!(0), ibig!(0), ibig!(0)]).equals_0());

        assert!(!VmTerm::Hash160([1; 20]).equals_0());
        assert!(!VmTerm::Hash256([1; 32]).equals_0());
        assert!(!VmTerm::Hash512([1; 64]).equals_0());
        assert!(!VmTerm::Unsigned8(1).equals_0());
        assert!(!VmTerm::Unsigned16(1).equals_0());
        assert!(!VmTerm::Unsigned32(1).equals_0());
        assert!(!VmTerm::Unsigned64(1).equals_0());
        assert!(!VmTerm::Unsigned128(1).equals_0());
        assert!(!VmTerm::UnsignedBig(ubig!(1)).equals_0());
        assert!(!VmTerm::Signed8(1).equals_0());
        assert!(!VmTerm::Signed16(1).equals_0());
        assert!(!VmTerm::Signed32(1).equals_0());
        assert!(!VmTerm::Signed64(1).equals_0());
        assert!(!VmTerm::Signed128(1).equals_0());
        assert!(!VmTerm::SignedBig(ibig!(1)).equals_0());
        assert!(!VmTerm::Hash160Array(vec![[0; 20], [1; 20], [0; 20]]).equals_0());
        assert!(!VmTerm::Hash256Array(vec![[0; 32], [0; 32], [1; 32], [0; 32]]).equals_0());
        assert!(
            !VmTerm::Hash512Array(vec![[0; 64], [0; 64], [0; 64], [1; 64], [0; 64]]).equals_0()
        );
        assert!(!VmTerm::Unsigned8Array(vec![0, 0, 0, 0, 1, 0]).equals_0());
        assert!(!VmTerm::Unsigned16Array(vec![0, 0, 0, 1, 0, 0, 0]).equals_0());
        assert!(!VmTerm::Unsigned32Array(vec![0, 0, 1, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(!VmTerm::Unsigned64Array(vec![0, 2, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(!VmTerm::Unsigned128Array(vec![3, 0, 0, 0, 0, 0, 0, 0]).equals_0());
        assert!(!VmTerm::UnsignedBigArray(vec![ubig!(1), ubig!(1), ubig!(1)]).equals_0());
        assert!(!VmTerm::Signed8Array(vec![0, 0, 0, 0, 0, 1]).equals_0());
        assert!(!VmTerm::Signed16Array(vec![0, 0, 0, 0, 2, 0, 0]).equals_0());
        assert!(!VmTerm::Signed32Array(vec![0, 0, 0, 0, 3, 0, 0, 0, 0]).equals_0());
        assert!(!VmTerm::Signed64Array(vec![0, 0, 0, 0, 0, 4, 0, 0, 0]).equals_0());
        assert!(!VmTerm::Signed128Array(vec![0, 0, 0, 0, 0, 0, 10, 0]).equals_0());
        assert!(!VmTerm::SignedBigArray(vec![ibig!(1), ibig!(1), ibig!(1)]).equals_0());
    }

    #[test]
    fn test_equals_1() {
        let mut arr_160: [u8; 20] = [0; 20];
        arr_160[0] = 0x01;
        let mut arr_256: [u8; 32] = [0; 32];
        arr_256[0] = 0x01;
        let mut arr_512: [u8; 64] = [0; 64];
        arr_512[0] = 0x01;

        assert!(VmTerm::Hash160(arr_160).equals_1());
        assert!(VmTerm::Hash256(arr_256).equals_1());
        assert!(VmTerm::Hash512(arr_512).equals_1());
        assert!(VmTerm::Unsigned8(1).equals_1());
        assert!(VmTerm::Unsigned16(1).equals_1());
        assert!(VmTerm::Unsigned32(1).equals_1());
        assert!(VmTerm::Unsigned64(1).equals_1());
        assert!(VmTerm::Unsigned128(1).equals_1());
        assert!(VmTerm::UnsignedBig(ubig!(1)).equals_1());
        assert!(VmTerm::Signed8(1).equals_1());
        assert!(VmTerm::Signed16(1).equals_1());
        assert!(VmTerm::Signed32(1).equals_1());
        assert!(VmTerm::Signed64(1).equals_1());
        assert!(VmTerm::Signed128(1).equals_1());
        assert!(VmTerm::SignedBig(ibig!(1)).equals_1());
        assert!(VmTerm::Hash160Array(vec![arr_160, arr_160, arr_160]).equals_1());
        assert!(VmTerm::Hash256Array(vec![arr_256, arr_256, arr_256, arr_256]).equals_1());
        assert!(VmTerm::Hash512Array(vec![arr_512, arr_512, arr_512, arr_512, arr_512]).equals_1());
        assert!(VmTerm::Unsigned8Array(vec![1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Unsigned16Array(vec![1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Unsigned32Array(vec![1, 1, 1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Unsigned64Array(vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Unsigned128Array(vec![1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::UnsignedBigArray(vec![ubig!(1), ubig!(1), ubig!(1)]).equals_1());
        assert!(VmTerm::Signed8Array(vec![1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Signed16Array(vec![1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Signed32Array(vec![1, 1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Signed64Array(vec![1, 1, 1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::Signed128Array(vec![1, 1, 1, 1, 1, 1, 1, 1]).equals_1());
        assert!(VmTerm::SignedBigArray(vec![ibig!(1), ibig!(1), ibig!(1)]).equals_1());

        assert!(!VmTerm::Hash160([0; 20]).equals_1());
        assert!(!VmTerm::Hash256([0; 32]).equals_1());
        assert!(!VmTerm::Hash512([0; 64]).equals_1());
        assert!(!VmTerm::Unsigned8(0).equals_1());
        assert!(!VmTerm::Unsigned16(0).equals_1());
        assert!(!VmTerm::Unsigned32(0).equals_1());
        assert!(!VmTerm::Unsigned64(0).equals_1());
        assert!(!VmTerm::Unsigned128(0).equals_1());
        assert!(!VmTerm::UnsignedBig(ubig!(0)).equals_1());
        assert!(!VmTerm::Signed8(0).equals_1());
        assert!(!VmTerm::Signed16(0).equals_1());
        assert!(!VmTerm::Signed32(0).equals_1());
        assert!(!VmTerm::Signed64(0).equals_1());
        assert!(!VmTerm::Signed128(0).equals_1());
        assert!(!VmTerm::SignedBig(ibig!(0)).equals_1());
        assert!(!VmTerm::Hash160Array(vec![[0; 20], arr_160, arr_160]).equals_1());
        assert!(!VmTerm::Hash256Array(vec![arr_256, arr_256, arr_256, [0; 32]]).equals_1());
        assert!(
            !VmTerm::Hash512Array(vec![arr_512, arr_512, [0; 64], arr_512, arr_512]).equals_1()
        );
        assert!(!VmTerm::Unsigned8Array(vec![1, 1, 0, 1, 1, 1]).equals_1());
        assert!(!VmTerm::Unsigned16Array(vec![1, 1, 1, 1, 1, 0, 1]).equals_1());
        assert!(!VmTerm::Unsigned32Array(vec![1, 1, 1, 0, 1, 1, 1, 1, 1]).equals_1());
        assert!(!VmTerm::Unsigned64Array(vec![1, 1, 1, 1, 1, 0, 0, 1, 1]).equals_1());
        assert!(!VmTerm::Unsigned128Array(vec![1, 1, 1, 1, 1, 1, 1, 0]).equals_1());
        assert!(!VmTerm::UnsignedBigArray(vec![ubig!(1), ubig!(1), ubig!(0)]).equals_1());
        assert!(!VmTerm::Signed8Array(vec![1, 1, 1, 1, 0, 1]).equals_1());
        assert!(!VmTerm::Signed16Array(vec![1, 1, 1, 1, 1, 0, 1]).equals_1());
        assert!(!VmTerm::Signed32Array(vec![1, 1, 1, 1, 1, 1, 1, 0, 0]).equals_1());
        assert!(!VmTerm::Signed64Array(vec![1, 1, 1, 1, 1, 1, 1, 1, 0]).equals_1());
        assert!(!VmTerm::Signed128Array(vec![1, 1, 1, 1, 1, 1, 0, 1]).equals_1());
        assert!(!VmTerm::SignedBigArray(vec![ibig!(1), ibig!(1), ibig!(0)]).equals_1());
    }

    #[test]
    fn test_is_comparable() {
        assert!(VmTerm::Hash160([1; 20]).is_comparable(&VmTerm::Hash160([2; 20])));
        assert!(VmTerm::Hash256([1; 32]).is_comparable(&VmTerm::Hash256([2; 32])));
        assert!(VmTerm::Hash512([1; 64]).is_comparable(&VmTerm::Hash512([2; 64])));
        assert!(VmTerm::Unsigned8(1_u8).is_comparable(&VmTerm::Unsigned8(2_u8)));
        assert!(VmTerm::Unsigned16(1_u16).is_comparable(&VmTerm::Unsigned16(2_u16)));
        assert!(VmTerm::Unsigned32(1_u32).is_comparable(&VmTerm::Unsigned32(2_u32)));
        assert!(VmTerm::Unsigned64(1_u64).is_comparable(&VmTerm::Unsigned64(2_u64)));
        assert!(VmTerm::Unsigned128(1_u128).is_comparable(&VmTerm::Unsigned128(2_u128)));
        assert!(VmTerm::UnsignedBig(ubig!(1)).is_comparable(&VmTerm::UnsignedBig(ubig!(2))));
        assert!(VmTerm::Signed8(1_i8).is_comparable(&VmTerm::Signed8(2_i8)));
        assert!(VmTerm::Signed16(1_i16).is_comparable(&VmTerm::Signed16(2_i16)));
        assert!(VmTerm::Signed32(1_i32).is_comparable(&VmTerm::Signed32(2_i32)));
        assert!(VmTerm::Signed64(1_i64).is_comparable(&VmTerm::Signed64(2_i64)));
        assert!(VmTerm::Signed128(1_i128).is_comparable(&VmTerm::Signed128(2_i128)));
        assert!(VmTerm::SignedBig(ibig!(1)).is_comparable(&VmTerm::SignedBig(ibig!(2))));

        assert!(VmTerm::Hash160Array(vec!([1; 20], [1; 20], [1; 20]))
            .is_comparable(&VmTerm::Hash160Array(vec!([2; 20], [2; 20], [2; 20]))));
        assert!(VmTerm::Hash256Array(vec!([1; 32], [1; 32], [1; 32]))
            .is_comparable(&VmTerm::Hash256Array(vec!([2; 32], [2; 32], [2; 32]))));
        assert!(VmTerm::Hash512Array(vec!([1; 64], [1; 64], [1; 64]))
            .is_comparable(&VmTerm::Hash512Array(vec!([2; 64], [2; 64], [2; 64]))));
        assert!(VmTerm::Unsigned8Array(vec!(1_u8, 1_u8))
            .is_comparable(&VmTerm::Unsigned8Array(vec!(2_u8, 2_u8))));
        assert!(VmTerm::Unsigned16Array(vec!(1_u16, 1_u16))
            .is_comparable(&VmTerm::Unsigned16Array(vec!(2_u16, 2_u16))));
        assert!(VmTerm::Unsigned32Array(vec!(1_u32, 1_u32))
            .is_comparable(&VmTerm::Unsigned32Array(vec!(2_u32, 2_u32))));
        assert!(VmTerm::Unsigned64Array(vec!(1_u64, 1_u64))
            .is_comparable(&VmTerm::Unsigned64Array(vec!(2_u64, 2_u64))));
        assert!(VmTerm::Unsigned128Array(vec!(1_u128, 1_u128))
            .is_comparable(&VmTerm::Unsigned128Array(vec!(2_u128, 2_u128))));
        assert!(VmTerm::UnsignedBigArray(vec!(ubig!(1), ubig!(1)))
            .is_comparable(&VmTerm::UnsignedBigArray(vec!(ubig!(2), ubig!(2)))));
        assert!(VmTerm::Signed8Array(vec!(1_i8, 1_i8))
            .is_comparable(&VmTerm::Signed8Array(vec!(2_i8, 2_i8))));
        assert!(VmTerm::Signed16Array(vec!(1_i16, 1_i16))
            .is_comparable(&VmTerm::Signed16Array(vec!(2_i16, 2_i16))));
        assert!(VmTerm::Signed32Array(vec!(1_i32, 1_i32))
            .is_comparable(&VmTerm::Signed32Array(vec!(2_i32, 2_i32))));
        assert!(VmTerm::Signed64Array(vec!(1_i64, 1_i64))
            .is_comparable(&VmTerm::Signed64Array(vec!(2_i64, 2_i64))));
        assert!(VmTerm::Signed128Array(vec!(1_i128, 1_i128))
            .is_comparable(&VmTerm::Signed128Array(vec!(2_i128, 2_i128))));
        assert!(VmTerm::SignedBigArray(vec!(ibig!(1), ibig!(1)))
            .is_comparable(&VmTerm::SignedBigArray(vec!(ibig!(2), ibig!(2)))));

        assert!(!VmTerm::Hash160Array(vec!([1; 20], [1; 20], [1; 20]))
            .is_comparable(&VmTerm::Hash160Array(vec!([2; 20]))));
        assert!(!VmTerm::Hash256Array(vec!([1; 32], [1; 32], [1; 32]))
            .is_comparable(&VmTerm::Hash256Array(vec!([2; 32], [2; 32]))));
        assert!(!VmTerm::Hash512Array(vec!([1; 64], [1; 64], [1; 64]))
            .is_comparable(&VmTerm::Hash512Array(vec!([2; 64]))));
        assert!(!VmTerm::Unsigned8Array(vec!(1_u8))
            .is_comparable(&VmTerm::Unsigned8Array(vec!(2_u8, 2_u8))));
        assert!(!VmTerm::Unsigned16Array(vec!(1_u16))
            .is_comparable(&VmTerm::Unsigned16Array(vec!(2_u16, 2_u16))));
        assert!(!VmTerm::Unsigned32Array(vec!(1_u32))
            .is_comparable(&VmTerm::Unsigned32Array(vec!(2_u32, 2_u32))));
        assert!(!VmTerm::Unsigned64Array(vec!(1_u64))
            .is_comparable(&VmTerm::Unsigned64Array(vec!(2_u64, 2_u64))));
        assert!(!VmTerm::Unsigned128Array(vec!(1_u128))
            .is_comparable(&VmTerm::Unsigned128Array(vec!(2_u128, 2_u128))));
        assert!(!VmTerm::UnsignedBigArray(vec!(ubig!(1)))
            .is_comparable(&VmTerm::UnsignedBigArray(vec!(ubig!(2), ubig!(2)))));
        assert!(!VmTerm::Signed8Array(vec!(1_i8))
            .is_comparable(&VmTerm::Signed8Array(vec!(2_i8, 2_i8))));
        assert!(!VmTerm::Signed16Array(vec!(1_i16))
            .is_comparable(&VmTerm::Signed16Array(vec!(2_i16, 2_i16))));
        assert!(!VmTerm::Signed32Array(vec!(1_i32))
            .is_comparable(&VmTerm::Signed32Array(vec!(2_i32, 2_i32))));
        assert!(!VmTerm::Signed64Array(vec!(1_i64))
            .is_comparable(&VmTerm::Signed64Array(vec!(2_i64, 2_i64))));
        assert!(!VmTerm::Signed128Array(vec!(1_i128))
            .is_comparable(&VmTerm::Signed128Array(vec!(2_i128, 2_i128))));
        assert!(!VmTerm::SignedBigArray(vec!(ibig!(1)))
            .is_comparable(&VmTerm::SignedBigArray(vec!(ibig!(2), ibig!(2)))));

        assert!(!VmTerm::Hash160([1; 20]).is_comparable(&VmTerm::Hash256([2; 32])));
        assert!(!VmTerm::Hash256([1; 32]).is_comparable(&VmTerm::Hash512([2; 64])));
        assert!(!VmTerm::Hash512([1; 64]).is_comparable(&VmTerm::Hash160([2; 20])));
        assert!(!VmTerm::Unsigned8(1_u8).is_comparable(&VmTerm::Unsigned16(2_u16)));
        assert!(!VmTerm::Unsigned16(1_u16).is_comparable(&VmTerm::Unsigned32(2_u32)));
        assert!(!VmTerm::Unsigned32(1_u32).is_comparable(&VmTerm::Unsigned64(2_u64)));
        assert!(!VmTerm::Unsigned64(1_u64).is_comparable(&VmTerm::Unsigned128(2_u128)));
        assert!(!VmTerm::Unsigned128(1_u128).is_comparable(&VmTerm::Unsigned8(2_u8)));
        assert!(!VmTerm::UnsignedBig(ubig!(1)).is_comparable(&VmTerm::SignedBig(ibig!(2))));
        assert!(!VmTerm::Unsigned8(1_u8).is_comparable(&VmTerm::Signed8(2_i8)));
        assert!(!VmTerm::Unsigned16(1_u16).is_comparable(&VmTerm::Signed16(2_i16)));
        assert!(!VmTerm::Unsigned32(1_u32).is_comparable(&VmTerm::Signed32(2_i32)));
        assert!(!VmTerm::Unsigned64(1_u64).is_comparable(&VmTerm::Signed64(2_i64)));
        assert!(!VmTerm::Unsigned128(1_u128).is_comparable(&VmTerm::Signed128(2_i128)));
        assert!(!VmTerm::UnsignedBig(ubig!(1)).is_comparable(&VmTerm::SignedBig(ibig!(2))));
        assert!(!VmTerm::Unsigned8(1_u8).is_comparable(&VmTerm::Signed128(2_i128)));
        assert!(!VmTerm::Unsigned16(1_u16).is_comparable(&VmTerm::Signed64(2_i64)));
        assert!(!VmTerm::Unsigned32(1_u32).is_comparable(&VmTerm::Signed32(2_i32)));
        assert!(!VmTerm::Unsigned64(1_u64).is_comparable(&VmTerm::Signed64(2_i64)));
        assert!(!VmTerm::Unsigned128(1_u128).is_comparable(&VmTerm::Signed128(2_i128)));
        assert!(!VmTerm::UnsignedBig(ubig!(1)).is_comparable(&VmTerm::SignedBig(ibig!(2))));
    }

    #[test]
    fn test_is_array() {
        assert!(!VmTerm::Hash160([0; 20]).is_array());
        assert!(!VmTerm::Hash256([0; 32]).is_array());
        assert!(!VmTerm::Hash512([0; 64]).is_array());
        assert!(!VmTerm::Unsigned8(0).is_array());
        assert!(!VmTerm::Unsigned16(0).is_array());
        assert!(!VmTerm::Unsigned32(0).is_array());
        assert!(!VmTerm::Unsigned64(0).is_array());
        assert!(!VmTerm::Unsigned128(0).is_array());
        assert!(!VmTerm::UnsignedBig(ubig!(0)).is_array());
        assert!(!VmTerm::Signed8(0).is_array());
        assert!(!VmTerm::Signed16(0).is_array());
        assert!(!VmTerm::Signed32(0).is_array());
        assert!(!VmTerm::Signed64(0).is_array());
        assert!(!VmTerm::Signed128(0).is_array());
        assert!(!VmTerm::SignedBig(ibig!(0)).is_array());
        assert!(VmTerm::Hash160Array(vec![[0; 20], [0; 20], [0; 20]]).is_array());
        assert!(VmTerm::Hash256Array(vec![[0; 32], [0; 32], [0; 32], [0; 32]]).is_array());
        assert!(VmTerm::Hash512Array(vec![[0; 64], [0; 64], [0; 64], [0; 64], [0; 64]]).is_array());
        assert!(VmTerm::Unsigned8Array(vec![0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Unsigned16Array(vec![0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Unsigned32Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Unsigned64Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Unsigned128Array(vec![0, 0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::UnsignedBigArray(vec![ubig!(0), ubig!(0), ubig!(0)]).is_array());
        assert!(VmTerm::Signed8Array(vec![0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Signed16Array(vec![0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Signed32Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Signed64Array(vec![0, 0, 0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::Signed128Array(vec![0, 0, 0, 0, 0, 0, 0, 0]).is_array());
        assert!(VmTerm::SignedBigArray(vec![ibig!(0), ibig!(0), ibig!(0)]).is_array());
    }

    #[test]
    fn test_vm_term_to_bytes_raw() {
        assert_eq!(VmTerm::Hash160([0; 20]).to_bytes_raw(), [0; 20]);
        assert_eq!(VmTerm::Hash256([0; 32]).to_bytes_raw(), [0; 32]);
        assert_eq!(VmTerm::Hash512([0; 64]).to_bytes_raw(), [0; 64]);
        assert_eq!(VmTerm::Unsigned8(0x01).to_bytes_raw(), [1]);
        assert_eq!(VmTerm::Unsigned16(0x01).to_bytes_raw(), [1, 0]);
        assert_eq!(VmTerm::Unsigned32(0x01).to_bytes_raw(), [1, 0, 0, 0]);
        assert_eq!(
            VmTerm::Unsigned64(0x01).to_bytes_raw(),
            [1, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Unsigned128(0x01).to_bytes_raw(),
            [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(VmTerm::UnsignedBig(ubig!(0x01)).to_bytes_raw(), [1]);
        assert_eq!(VmTerm::Signed8(0x01).to_bytes_raw(), [1]);
        assert_eq!(VmTerm::Signed8(-1).to_bytes_raw(), [255]);
        assert_eq!(VmTerm::Signed16(0x01).to_bytes_raw(), [1, 0]);
        assert_eq!(VmTerm::Signed32(0x01).to_bytes_raw(), [1, 0, 0, 0]);
        assert_eq!(
            VmTerm::Signed64(0x01).to_bytes_raw(),
            [1, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Signed128(-2).to_bytes_raw(),
            [254, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]
        );
        assert_eq!(
            VmTerm::Signed128(1).to_bytes_raw(),
            [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Signed128(0).to_bytes_raw(),
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(VmTerm::SignedBig(ibig!(0x01)).to_bytes_raw(), [1, 1]);
        assert_eq!(VmTerm::SignedBig(ibig!(-1)).to_bytes_raw(), [1, 255]);
        assert_eq!(VmTerm::SignedBig(ibig!(0)).to_bytes_raw(), [0]);
        assert_eq!(
            VmTerm::Hash160Array(vec![[0; 20], [0; 20], [0; 20]]).to_bytes_raw(),
            [0; 60]
        );
        assert_eq!(
            VmTerm::Hash256Array(vec![[0; 32], [0; 32], [0; 32], [0; 32]]).to_bytes_raw(),
            [0; 128]
        );
        assert_eq!(
            VmTerm::Hash512Array(vec![[0; 64], [0; 64], [0; 64], [0; 64], [0; 64]]).to_bytes_raw(),
            [0; 320]
        );
        assert_eq!(
            VmTerm::Unsigned8Array(vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06]).to_bytes_raw(),
            [1, 2, 3, 4, 5, 6]
        );
        assert_eq!(
            VmTerm::Unsigned16Array(vec![0x01, 0x02]).to_bytes_raw(),
            [1, 0, 2, 0]
        );
        assert_eq!(
            VmTerm::Unsigned32Array(vec![0x01, 0x02]).to_bytes_raw(),
            [1, 0, 0, 0, 2, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Unsigned64Array(vec![0x01, 0x02]).to_bytes_raw(),
            [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Unsigned128Array(vec![0x01, 0x02]).to_bytes_raw(),
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]
        );
        assert_eq!(
            VmTerm::UnsignedBigArray(vec![ubig!(0x01), ubig!(0x02)]).to_bytes_raw(),
            [1, 2]
        );
        assert_eq!(
            VmTerm::Signed8Array(vec![-6, 2, -1]).to_bytes_raw(),
            [250, 2, 255]
        );
        assert_eq!(
            VmTerm::Signed16Array(vec![0x01, 0x02]).to_bytes_raw(),
            [1, 0, 2, 0]
        );
        assert_eq!(
            VmTerm::Signed32Array(vec![0x01, 0x02]).to_bytes_raw(),
            [1, 0, 0, 0, 2, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Signed64Array(vec![0x01, 0x02]).to_bytes_raw(),
            [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        );
        assert_eq!(
            VmTerm::Signed128Array(vec![0x01, 0x02]).to_bytes_raw(),
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]
        );
        assert_eq!(
            VmTerm::SignedBigArray(vec![ibig!(0x01), ibig!(0x02)]).to_bytes_raw(),
            [1, 1, 2, 1]
        );
        assert_eq!(
            VmTerm::SignedBigArray(vec![ibig!(-1), ibig!(0x02)]).to_bytes_raw(),
            [1, 255, 2, 1]
        );
        assert_eq!(
            VmTerm::Hash160Array(vec![[0; 20], [0; 20], [0; 20]]).to_bytes_raw(),
            [0; 60]
        );
        assert_eq!(
            VmTerm::Hash256Array(vec![[0; 32], [0; 32], [0; 32], [0; 32]]).to_bytes_raw(),
            [0; 128]
        );
        assert_eq!(
            VmTerm::Hash512Array(vec![[0; 64], [0; 64], [0; 64], [0; 64], [0; 64]]).to_bytes_raw(),
            [0; 320]
        );
    }
}
