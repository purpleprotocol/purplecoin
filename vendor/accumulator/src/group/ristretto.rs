//! Ristretto group implementation (based on the `curve25519-dalek` crate).
use super::{Group, ToInteger, UnknownOrderGroup};
use crate::group::Codec;
use crate::util::{int, TypeRep};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use rug::integer::Order;
use rug::ops::Pow;
use rug::Integer;
use std::hash::{Hash, Hasher};

#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// Ristretto group implementation (based on the `curve25519-dalek` crate).
pub enum Ristretto {}

lazy_static! {
    pub static ref MAX_SAFE_EXPONENT: Integer = int(2).pow(255) - 1;
    pub static ref MAX_SAFE_SCALAR: Scalar = {
        let mut digits: [u8; 32] = [0; 32];
        MAX_SAFE_EXPONENT.write_digits(&mut digits, Order::LsfLe);
        Scalar::from_bytes_mod_order(digits)
    };
}

impl Ristretto {
    fn max_safe_exponent() -> &'static Integer {
        &MAX_SAFE_EXPONENT
    }
}

// REVIEW: Ideally we'd just use `RistrettoPoint` here, but only traits defined in this crate can
// be implemented for arbitrary types. How to fix without wrapping?
//
// It may make sense to fork `curve25519-dalek` to add the `Hash` impl. Then we won't need to wrap.
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Debug, PartialEq, Eq)]
/// A Ristretto group element, directly wrapping a Ristretto point.
pub struct RistrettoElem(RistrettoPoint);

#[allow(clippy::derived_hash_with_manual_eq)]
impl Hash for RistrettoElem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.compress().as_bytes().hash(state);
    }
}

impl Codec for RistrettoElem {
    fn to_bytes(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn from_bytes(_bytes: &[u8]) -> Result<Self, &'static str> {
        unimplemented!()
    }
}

impl TypeRep for Ristretto {
    type Rep = ();
    fn rep() -> &'static Self::Rep {
        &()
    }
}

impl Group for Ristretto {
    type Elem = RistrettoElem;

    fn op_(_: &(), a: &RistrettoElem, b: &RistrettoElem) -> RistrettoElem {
        RistrettoElem(a.0 + b.0)
    }

    fn id_(_: &()) -> RistrettoElem {
        RistrettoElem(RistrettoPoint::identity())
    }

    fn inv_(_: &(), x: &RistrettoElem) -> RistrettoElem {
        RistrettoElem(-x.0)
    }

    fn exp_(_: &(), x: &RistrettoElem, n: &Integer) -> RistrettoElem {
        let mut remaining = n.clone();
        let mut result = Self::id();

        while remaining > *MAX_SAFE_EXPONENT {
            result = RistrettoElem(result.0 + x.0 * (*MAX_SAFE_SCALAR));
            remaining -= Self::max_safe_exponent();
        }

        let mut digits: [u8; 32] = [0; 32];
        remaining.write_digits(&mut digits, Order::LsfLe);
        let factor = Scalar::from_bytes_mod_order(digits);
        RistrettoElem(result.0 + x.0 * factor)
    }
}

impl ToInteger for RistrettoElem {
    fn to_integer(&self) -> Integer {
        unimplemented!()
    }
}

impl From<Integer> for RistrettoElem {
    fn from(_other: Integer) -> Self {
        unimplemented!()
    }
}

impl UnknownOrderGroup for Ristretto {
    fn unknown_order_elem_(_: &()) -> RistrettoElem {
        RistrettoElem(curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::int;
    use curve25519_dalek::constants;

    #[test]
    fn test_inv() {
        let bp = RistrettoElem(constants::RISTRETTO_BASEPOINT_POINT);
        let bp_inv = Ristretto::inv(&bp);
        assert!(Ristretto::op(&bp, &bp_inv) == Ristretto::id());
        assert_ne!(bp, bp_inv);
    }

    #[test]
    fn test_exp() {
        let bp = RistrettoElem(constants::RISTRETTO_BASEPOINT_POINT);
        let exp_a = Ristretto::exp(&bp, &int(2).pow(258));
        let exp_b = Ristretto::exp(&bp, &int(2).pow(257));
        let exp_b_2 = Ristretto::exp(&exp_b, &int(2));
        assert_eq!(exp_a, exp_b_2);
    }
}
