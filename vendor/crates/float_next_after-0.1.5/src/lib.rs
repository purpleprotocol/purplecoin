#![allow(clippy::float_cmp)]

use num_traits::Float;
use std::{f32, f64};

/// Returns the next representable float value in the direction of y
///
/// This function is strict and will step to the very next representable floating point,
/// even if that value is subnormal.
///
/// Base assumptions:
///
/// self == y -> return y
///
/// self >= positive infinity -> return positive infinity
///
/// self <= negative infinity -> return negative infinity
///
/// self == NaN -> return NaN
///
/// self == -0.0 and y == 0.0 -> return positive 0.0
///
/// self == -0.0 and y == positive infinity -> 5e-324
///
/// # Examples
///
/// ```
/// use float_next_after::NextAfter;
///
/// // Large numbers
/// let big_num = 16237485966.00000437586943_f64;
/// let next = big_num.next_after(std::f64::INFINITY);
/// assert_eq!(next, 16237485966.000006_f64);
///
/// // Expected handling of 1.0
/// let one = 1_f64;
/// let next = one.next_after(std::f64::INFINITY);
/// assert_eq!(next, 1_f64 + std::f64::EPSILON);
///
/// // Tiny (negative) numbers
/// let zero = 0_f32;
/// let next = zero.next_after(std::f32::NEG_INFINITY);
/// assert_eq!(next, -0.000000000000000000000000000000000000000000001_f32);
///
/// // Equal source/dest (even -0 == 0)
/// let zero = 0_f64;
/// let next = zero.next_after(-0_f64);
/// assert_eq!(next, -0_f64);
/// ```
///
/// # Safety
///
/// This trait uses the ToBits and FromBits functions from f32 and f64.
/// Those both use unsafe { mem::transmute(self) } / unsafe { mem::transmute(v) }
/// to convert a f32/f64 to u32/u64.  The docs for those functions claim they are safe
/// and that "the safety issues with sNaN were overblown!"
///
pub trait NextAfter<T: Float> {
    fn next_after(self, y: T) -> T;
}

// Note: I made separate implementations for f32 and f64 in order to make the bit
// conversion explicit to anyone else who might come along to look at this. The f64
// is converted to u64, incremented by one, then converted back to f64. The f32
// is converted to u32, incremented by one, then converted back to f32.
impl NextAfter<f64> for f64 {
    fn next_after(self, y: f64) -> f64 {
        if let Some(out) = short_circuit_operands(self, y) {
            return out;
        }

        let zero = 0_f64;

        if self == zero {
            let return_value = f64::from_bits(1);
            copy_sign(return_value, y)
        } else {
            // Use trick f64 -> u64 +- 1 -> f64; increment or decrement depending on same sign.
            let return_value = if (y > self) == (self > zero) {
                f64::from_bits(self.to_bits() + 1)
            } else {
                f64::from_bits(self.to_bits() - 1)
            };
            // If return value is zero remember its original sign.
            if return_value != zero {
                return_value
            } else {
                copy_sign(return_value, self)
            }
        }
    }
}

impl NextAfter<f32> for f32 {
    fn next_after(self, y: f32) -> f32 {
        if let Some(out) = short_circuit_operands(self, y) {
            return out;
        }

        let zero = 0_f32;

        if self == zero {
            let return_value = f32::from_bits(1);
            copy_sign(return_value, y)
        } else {
            // Use trick f64 -> u64 +- 1 -> f64; increment or decrement depending on same sign.
            let return_value = if (y > self) == (self > zero) {
                f32::from_bits(self.to_bits() + 1)
            } else {
                f32::from_bits(self.to_bits() - 1)
            };
            // If return value is zero remember its original sign.
            if return_value != zero {
                return_value
            } else {
                copy_sign(return_value, self)
            }
        }
    }
}

#[inline]
fn short_circuit_operands<T: Float>(x: T, y: T) -> Option<T> {
    // If x and y are equal (also -0_f64 == 0_f64 in rust), there is nothing further to do
    if y == x {
        // The policy is to return y in cases of equality,
        // this only matters when x = 0.0 and y = -0.0 (or the reverse)
        return Some(y);
    }

    // If x or y is NaN return NaN
    if x.is_nan() || y.is_nan() {
        return Some(T::nan());
    }

    // If x is infinite or somehow greater
    if x >= T::infinity() {
        return Some(T::infinity());
    }

    // If x is negative infinite or somehow lower
    if x <= T::neg_infinity() {
        return Some(T::neg_infinity());
    }

    None
}

#[inline]
fn copy_sign<T: Float>(x: T, y: T) -> T {
    if x.is_sign_positive() == y.is_sign_positive() {
        x
    } else {
        -x
    }
}

#[cfg(test)]
mod tests_f64 {
    use super::*;

    type T = f64;

    const POS_INF: T = std::f64::INFINITY;
    const NEG_INF: T = std::f64::NEG_INFINITY;
    const POS_ZERO: T = 0.0;
    const NEG_ZERO: T = -0.0;

    // Note: Not the same as f64::MIN_POSITIVE, because that is only the min *normal* number.
    const SMALLEST_POS: T = 5e-324;
    const SMALLEST_NEG: T = -5e-324;
    const LARGEST_POS: T = std::f64::MAX;
    const LARGEST_NEG: T = std::f64::MIN;

    const POS_ONE: T = 1.0;
    const NEG_ONE: T = -1.0;
    const NEXT_LARGER_THAN_ONE: T = 1.0 + std::f64::EPSILON;
    const NEXT_SMALLER_THAN_ONE: T = 0.999_999_999_999_999_9;

    const SEQUENCE_BIG_NUM: (T, T) = (16_237_485_966.000_004, 16_237_485_966.000_006);

    const NAN: T = std::f64::NAN;

    fn is_pos_zero(x: T) -> bool {
        x.to_bits() == POS_ZERO.to_bits()
    }

    fn is_neg_zero(x: T) -> bool {
        x.to_bits() == NEG_ZERO.to_bits()
    }

    #[test]
    fn test_copy_sign() {
        assert_eq!(copy_sign(POS_ONE, POS_ZERO), POS_ONE);
        assert_eq!(copy_sign(NEG_ONE, POS_ZERO), POS_ONE);
        assert_eq!(copy_sign(POS_ONE, NEG_ZERO), NEG_ONE);
        assert_eq!(copy_sign(NEG_ONE, NEG_ZERO), NEG_ONE);
    }

    #[test]
    fn verify_constants() {
        assert_ne!(POS_ZERO.to_bits(), NEG_ZERO.to_bits());
        assert!(SMALLEST_POS > POS_ZERO);
        assert!(SMALLEST_NEG < NEG_ZERO);
        assert!(!SMALLEST_POS.is_normal());
        assert!(!SMALLEST_NEG.is_normal());
    }

    #[test]
    fn next_larger_than_0() {
        assert_eq!(POS_ZERO.next_after(POS_INF), SMALLEST_POS);
        assert_eq!(NEG_ZERO.next_after(POS_INF), SMALLEST_POS);
    }

    #[test]
    fn next_smaller_than_0() {
        assert_eq!(POS_ZERO.next_after(NEG_INF), SMALLEST_NEG);
        assert_eq!(NEG_ZERO.next_after(NEG_INF), SMALLEST_NEG);
    }

    #[test]
    fn step_towards_zero() {
        // For steps towards zero, the sign of the zero reflects the direction
        // from where zero was approached.
        assert!(is_pos_zero(SMALLEST_POS.next_after(POS_ZERO)));
        assert!(is_pos_zero(SMALLEST_POS.next_after(NEG_ZERO)));
        assert!(is_pos_zero(SMALLEST_POS.next_after(NEG_INF)));
        assert!(is_neg_zero(SMALLEST_NEG.next_after(NEG_ZERO)));
        assert!(is_neg_zero(SMALLEST_NEG.next_after(POS_ZERO)));
        assert!(is_neg_zero(SMALLEST_NEG.next_after(POS_INF)));
    }

    #[test]
    fn special_case_signed_zeros() {
        // For a non-zero dest, stepping away from either POS_ZERO or NEG_ZERO
        // has a non-zero result. Only if the destination itself points to the
        // "other zero", the next_after call performs a zero sign switch.
        assert!(is_neg_zero(POS_ZERO.next_after(NEG_ZERO)));
        assert!(is_pos_zero(NEG_ZERO.next_after(POS_ZERO)));
    }

    #[test]
    fn nextafter_around_one() {
        assert_eq!(POS_ONE.next_after(POS_INF), NEXT_LARGER_THAN_ONE);
        assert_eq!(POS_ONE.next_after(NEG_INF), NEXT_SMALLER_THAN_ONE);
        assert_eq!(NEG_ONE.next_after(NEG_INF), -NEXT_LARGER_THAN_ONE);
        assert_eq!(NEG_ONE.next_after(POS_INF), -NEXT_SMALLER_THAN_ONE);
    }

    #[test]
    fn nextafter_for_big_pos_number() {
        let (lo, hi) = SEQUENCE_BIG_NUM;
        assert_eq!(lo.next_after(POS_INF), hi);
        assert_eq!(hi.next_after(NEG_INF), lo);
        assert_eq!(lo.next_after(hi), hi);
        assert_eq!(hi.next_after(lo), lo);
    }

    #[test]
    fn nextafter_for_big_neg_number() {
        let (lo, hi) = SEQUENCE_BIG_NUM;
        let (lo, hi) = (-lo, -hi);
        assert_eq!(lo.next_after(NEG_INF), hi);
        assert_eq!(hi.next_after(POS_INF), lo);
        assert_eq!(lo.next_after(hi), hi);
        assert_eq!(hi.next_after(lo), lo);
    }

    #[test]
    fn step_to_largest_is_possible() {
        let smaller = LARGEST_POS.next_after(NEG_INF);
        assert_eq!(smaller.next_after(POS_INF), LARGEST_POS);
        let smaller = LARGEST_NEG.next_after(POS_INF);
        assert_eq!(smaller.next_after(NEG_INF), LARGEST_NEG);
    }

    #[test]
    fn jump_to_infinity() {
        // Incrementing the max representable number has to go to infinity.
        assert_eq!(LARGEST_POS.next_after(POS_INF), POS_INF);
        assert_eq!(LARGEST_NEG.next_after(NEG_INF), NEG_INF);
    }

    #[test]
    fn stays_at_infinity() {
        // Once infinity is reached, there is not going back to normal numbers
        assert_eq!(POS_INF.next_after(NEG_INF), POS_INF);
        assert_eq!(NEG_INF.next_after(POS_INF), NEG_INF);
    }

    #[test]
    fn returns_nan_for_any_nan_involved() {
        assert!(NAN.next_after(POS_ONE).is_nan());
        assert!(POS_ONE.next_after(NAN).is_nan());
        assert!(NAN.next_after(NAN).is_nan());
    }

    #[test]
    fn returns_identity_for_equal_dest() {
        let values = [
            POS_ZERO,
            NEG_ZERO,
            POS_ONE,
            NEG_ONE,
            SEQUENCE_BIG_NUM.0,
            SEQUENCE_BIG_NUM.1,
            POS_INF,
            NEG_INF,
            SMALLEST_POS,
            SMALLEST_NEG,
            LARGEST_POS,
            LARGEST_NEG,
        ];
        for x in values.iter() {
            assert_eq!(x.next_after(*x), *x);
        }
    }

    #[test]
    fn roundtrip() {
        let values = [
            POS_ONE,
            NEG_ONE,
            SEQUENCE_BIG_NUM.0,
            SEQUENCE_BIG_NUM.1,
            SMALLEST_POS,
            SMALLEST_NEG,
        ];
        for orig in values.to_vec() {
            assert_eq!(orig.next_after(POS_INF).next_after(NEG_INF), orig);
            assert_eq!(orig.next_after(NEG_INF).next_after(POS_INF), orig);

            let upper = orig.next_after(POS_INF);
            let lower = orig.next_after(NEG_INF);

            assert_eq!(orig.next_after(upper).next_after(lower), orig);
            assert_eq!(orig.next_after(lower).next_after(upper), orig);
        }
    }
}

#[cfg(test)]
mod tests_f32 {
    use super::*;

    type T = f32;

    const POS_INF: T = std::f32::INFINITY;
    const NEG_INF: T = std::f32::NEG_INFINITY;
    const POS_ZERO: T = 0.0;
    const NEG_ZERO: T = -0.0;

    // Note: Not the same as f32::MIN_POSITIVE, because that is only the min *normal* number.
    const SMALLEST_POS: T = 1e-45;
    const SMALLEST_NEG: T = -1e-45;
    const LARGEST_POS: T = std::f32::MAX;
    const LARGEST_NEG: T = std::f32::MIN;

    const POS_ONE: T = 1.0;
    const NEG_ONE: T = -1.0;
    const NEXT_LARGER_THAN_ONE: T = 1.0 + std::f32::EPSILON;
    const NEXT_SMALLER_THAN_ONE: T = 0.999_999_94;

    const SEQUENCE_BIG_NUM: (T, T) = (1.230_000_1e34, 1.230_000_3e34);

    const NAN: T = std::f32::NAN;

    fn is_pos_zero(x: T) -> bool {
        x.to_bits() == POS_ZERO.to_bits()
    }

    fn is_neg_zero(x: T) -> bool {
        x.to_bits() == NEG_ZERO.to_bits()
    }

    #[test]
    fn test_copy_sign() {
        assert_eq!(copy_sign(POS_ONE, POS_ZERO), POS_ONE);
        assert_eq!(copy_sign(NEG_ONE, POS_ZERO), POS_ONE);
        assert_eq!(copy_sign(POS_ONE, NEG_ZERO), NEG_ONE);
        assert_eq!(copy_sign(NEG_ONE, NEG_ZERO), NEG_ONE);
    }

    #[test]
    fn verify_constants() {
        assert_ne!(POS_ZERO.to_bits(), NEG_ZERO.to_bits());
        assert!(SMALLEST_POS > POS_ZERO);
        assert!(SMALLEST_NEG < NEG_ZERO);
        assert!(!SMALLEST_POS.is_normal());
        assert!(!SMALLEST_NEG.is_normal());
    }

    #[test]
    fn next_larger_than_0() {
        assert_eq!(POS_ZERO.next_after(POS_INF), SMALLEST_POS);
        assert_eq!(NEG_ZERO.next_after(POS_INF), SMALLEST_POS);
    }

    #[test]
    fn next_smaller_than_0() {
        assert_eq!(POS_ZERO.next_after(NEG_INF), SMALLEST_NEG);
        assert_eq!(NEG_ZERO.next_after(NEG_INF), SMALLEST_NEG);
    }

    #[test]
    fn step_towards_zero() {
        // For steps towards zero, the sign of the zero reflects the direction
        // from where zero was approached.
        assert!(is_pos_zero(SMALLEST_POS.next_after(POS_ZERO)));
        assert!(is_pos_zero(SMALLEST_POS.next_after(NEG_ZERO)));
        assert!(is_pos_zero(SMALLEST_POS.next_after(NEG_INF)));
        assert!(is_neg_zero(SMALLEST_NEG.next_after(NEG_ZERO)));
        assert!(is_neg_zero(SMALLEST_NEG.next_after(POS_ZERO)));
        assert!(is_neg_zero(SMALLEST_NEG.next_after(POS_INF)));
    }

    #[test]
    fn special_case_signed_zeros() {
        // For a non-zero dest, stepping away from either POS_ZERO or NEG_ZERO
        // has a non-zero result. Only if the destination itself points to the
        // "other zero", the next_after call performs a zero sign switch.
        assert!(is_neg_zero(POS_ZERO.next_after(NEG_ZERO)));
        assert!(is_pos_zero(NEG_ZERO.next_after(POS_ZERO)));
    }

    #[test]
    fn nextafter_around_one() {
        assert_eq!(POS_ONE.next_after(POS_INF), NEXT_LARGER_THAN_ONE);
        assert_eq!(POS_ONE.next_after(NEG_INF), NEXT_SMALLER_THAN_ONE);
        assert_eq!(NEG_ONE.next_after(NEG_INF), -NEXT_LARGER_THAN_ONE);
        assert_eq!(NEG_ONE.next_after(POS_INF), -NEXT_SMALLER_THAN_ONE);
    }

    #[test]
    fn nextafter_for_big_pos_number() {
        let (lo, hi) = SEQUENCE_BIG_NUM;
        assert_eq!(lo.next_after(POS_INF), hi);
        assert_eq!(hi.next_after(NEG_INF), lo);
        assert_eq!(lo.next_after(hi), hi);
        assert_eq!(hi.next_after(lo), lo);
    }

    #[test]
    fn nextafter_for_big_neg_number() {
        let (lo, hi) = SEQUENCE_BIG_NUM;
        let (lo, hi) = (-lo, -hi);
        assert_eq!(lo.next_after(NEG_INF), hi);
        assert_eq!(hi.next_after(POS_INF), lo);
        assert_eq!(lo.next_after(hi), hi);
        assert_eq!(hi.next_after(lo), lo);
    }

    #[test]
    fn step_to_largest_is_possible() {
        let smaller = LARGEST_POS.next_after(NEG_INF);
        assert_eq!(smaller.next_after(POS_INF), LARGEST_POS);
        let smaller = LARGEST_NEG.next_after(POS_INF);
        assert_eq!(smaller.next_after(NEG_INF), LARGEST_NEG);
    }

    #[test]
    fn jump_to_infinity() {
        // Incrementing the max representable number has to go to infinity.
        assert_eq!(LARGEST_POS.next_after(POS_INF), POS_INF);
        assert_eq!(LARGEST_NEG.next_after(NEG_INF), NEG_INF);
    }

    #[test]
    fn stays_at_infinity() {
        // Once infinity is reached, there is not going back to normal numbers
        assert_eq!(POS_INF.next_after(NEG_INF), POS_INF);
        assert_eq!(NEG_INF.next_after(POS_INF), NEG_INF);
    }

    #[test]
    fn returns_nan_for_any_nan_involved() {
        assert!(NAN.next_after(POS_ONE).is_nan());
        assert!(POS_ONE.next_after(NAN).is_nan());
        assert!(NAN.next_after(NAN).is_nan());
    }

    #[test]
    fn returns_identity_for_equal_dest() {
        let values = [
            POS_ZERO,
            NEG_ZERO,
            POS_ONE,
            NEG_ONE,
            SEQUENCE_BIG_NUM.0,
            SEQUENCE_BIG_NUM.1,
            POS_INF,
            NEG_INF,
            SMALLEST_POS,
            SMALLEST_NEG,
            LARGEST_POS,
            LARGEST_NEG,
        ];
        for x in values.iter() {
            assert_eq!(x.next_after(*x), *x);
        }
    }

    #[test]
    fn roundtrip() {
        let values = [
            POS_ONE,
            NEG_ONE,
            SEQUENCE_BIG_NUM.0,
            SEQUENCE_BIG_NUM.1,
            SMALLEST_POS,
            SMALLEST_NEG,
        ];
        for orig in values.to_vec() {
            assert_eq!(orig.next_after(POS_INF).next_after(NEG_INF), orig);
            assert_eq!(orig.next_after(NEG_INF).next_after(POS_INF), orig);

            let upper = orig.next_after(POS_INF);
            let lower = orig.next_after(NEG_INF);

            assert_eq!(orig.next_after(upper).next_after(lower), orig);
            assert_eq!(orig.next_after(lower).next_after(upper), orig);
        }
    }
}
