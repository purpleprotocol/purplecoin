//! Miscellaneous functions used throughout the library.
use crate::group::Group;
use crate::hash::hash_to_prime;
use rug::Integer;
use std::hash::Hash;
use rayon::prelude::*;

/// Pseudo-type-level programming.
/// This trait allows us to reflect "type-level" (i.e. static) information at runtime.
pub trait TypeRep: 'static {
  /// The associated type of the simulated type-level static information.
  type Rep: 'static;

  /// Returns the static data for the type.
  fn rep() -> &'static Self::Rep;
}

/// Convenience wrapper for creating `Rug` integers.
pub fn int<T>(val: T) -> Integer
where
  Integer: From<T>,
{
  Integer::from(val)
}

/// Hashes its arguments to primes and takes their product.
pub fn prime_hash_product<T: Hash + Sync>(ts: &[T]) -> Integer {
  ts.par_iter().map(hash_to_prime).product()
}

/// Computes the `(xy)`th root of `g` given the `x`th and `y`th roots of `g` and `(x, y)` coprime.
// TODO: Consider moving this to the `accumulator` module?
#[allow(clippy::similar_names)]
pub fn shamir_trick<G: Group>(
  xth_root: &G::Elem,
  yth_root: &G::Elem,
  x: &Integer,
  y: &Integer,
) -> Option<G::Elem> {
  #[cfg(debug_assertions)]
  let (a, b) = rayon::join(|| G::exp(xth_root, x), || G::exp(yth_root, y));

  #[cfg(debug_assertions)]
  if a != b {
    return None;
  }

  let (gcd, a, b) = <(Integer, Integer, Integer)>::from(x.gcd_cofactors_ref(&y));

  #[cfg(debug_assertions)]
  if gcd != int(1) {
    return None;
  }

  let (a, b) = rayon::join(|| G::exp(xth_root, &b), || G::exp(yth_root, &a));

  Some(G::op(&a, &b))
}

/// Solves a linear congruence of form `ax = b mod m` for the set of solutions `x`. Solution sets
/// are characterized by integers `mu` and `v` s.t. `x = mu + vn` and `n` is any integer.
pub fn solve_linear_congruence(
  a: &Integer,
  b: &Integer,
  m: &Integer,
) -> Option<(Integer, Integer)> {
  // g = gcd(a, m) => da + em = g
  let (g, d, _) = <(Integer, Integer, Integer)>::from(a.gcd_cofactors_ref(m));

  // q = floor_div(b, g)
  // r = b % g
  let (q, r) = <(Integer, Integer)>::from(b.div_rem_floor_ref(&g));
  if r != 0 {
    return None;
  }

  let mu = (q * d) % m;
  let v = m / g;
  Some((mu, v))
}

/// Folds over `xs` but in a divide-and-conquer fashion: Instead of `F(F(F(F(acc, a), b), c), d))`
/// this computes `F(acc, F(F(a, b), F(c, d)))`.
pub fn divide_and_conquer<G: Group, E>(acc: (Integer, G::Elem), xs: &[(Integer, G::Elem)]) -> Result<(Integer, G::Elem), E>
{
  if xs.is_empty() {
    return Ok(acc);
  }

  Ok(xs.par_iter().cloned().reduce(|| acc.clone(), |(p1, v1), (p2, v2)| {
    let r = shamir_trick::<G>(&v1, &v2, &p1, &p2).unwrap();
    (int(p1 * p2), r)
  }))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::group::{Group, Rsa2048, UnknownOrderGroup};
  use crate::util::int;

  #[derive(Debug)]
  enum Never {}

  /// Merge-based computation of `Integer` array products. Faster than  the iterative
  /// `iter.product()` for really large integers.
  fn merge_product(xs: &[Integer]) -> Integer {
    divide_and_conquer(
      |a, b| -> Result<Integer, Never> { Ok(int(a * b)) },
      int(1),
      &xs,
    )
    .unwrap()
  }

  #[test]
  fn test_linear_congruence_solver() {
    assert_eq!(
      (Integer::from(-2), Integer::from(4)),
      solve_linear_congruence(&Integer::from(3), &Integer::from(2), &Integer::from(4)).unwrap()
    );

    assert_eq!(
      (Integer::from(-2), Integer::from(4)),
      solve_linear_congruence(&Integer::from(3), &Integer::from(2), &Integer::from(4)).unwrap()
    );

    assert_eq!(
      (Integer::from(1), Integer::from(2)),
      solve_linear_congruence(&Integer::from(5), &Integer::from(1), &Integer::from(2)).unwrap()
    );

    assert_eq!(
      (Integer::from(-3), Integer::from(5)),
      solve_linear_congruence(&Integer::from(2), &Integer::from(4), &Integer::from(5)).unwrap()
    );

    assert_eq!(
      (Integer::from(2491), Integer::from(529)),
      solve_linear_congruence(
        &Integer::from(230),
        &Integer::from(1081),
        &Integer::from(12167)
      )
      .unwrap()
    );
  }

  #[test]
  fn test_linear_congruence_solver_no_solution() {
    // Let `g = gcd(a, m)`. If `b` is not divisible by `g`, there are no solutions. If `b` is
    // divisible by `g`, there are `g` solutions.
    let result =
      solve_linear_congruence(&Integer::from(33), &Integer::from(7), &Integer::from(143));
    assert!(result.is_none());

    let result =
      solve_linear_congruence(&Integer::from(13), &Integer::from(14), &Integer::from(39));
    assert!(result.is_none());
  }

  #[test]
  fn test_shamir_trick() {
    let (x, y, z) = (&int(13), &int(17), &int(19));
    let xth_root = Rsa2048::exp(&Rsa2048::unknown_order_elem(), &int(y * z));
    let yth_root = Rsa2048::exp(&Rsa2048::unknown_order_elem(), &int(x * z));
    let xyth_root = Rsa2048::exp(&Rsa2048::unknown_order_elem(), z);
    assert!(shamir_trick::<Rsa2048>(&xth_root, &yth_root, x, y) == Some(xyth_root));
  }

  #[test]
  fn test_shamir_trick_failure() {
    let (x, y, z) = (&int(7), &int(14), &int(19)); // Inputs not coprime.
    let xth_root = Rsa2048::exp(&Rsa2048::unknown_order_elem(), &int(y * z));
    let yth_root = Rsa2048::exp(&Rsa2048::unknown_order_elem(), &int(x * z));
    assert!(shamir_trick::<Rsa2048>(&xth_root, &yth_root, x, y) == None);
  }

  #[test]
  fn test_merge_product() {
    let ints = vec![int(3), int(5), int(7), int(9), int(11)];
    assert!(merge_product(&ints) == int(10395));
  }
}
