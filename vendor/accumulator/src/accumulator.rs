//! Accumulator library, built on a generic group interface.
use crate::group::{Codec, UnknownOrderGroup};
use crate::hash::hash_to_prime;
use crate::proof::{Poe, Poke2};
use crate::util::{divide_and_conquer, int, prime_hash_product};
use rayon::prelude::*;
use rug::Integer;
use std::hash::Hash;
use std::marker::PhantomData;

#[derive(Debug)]
/// The different types of accumulator errors.
pub enum AccError {
    /// Bad witness.
    BadWitness,

    /// Error when updating a witness.
    BadWitnessUpdate,

    /// Division by zero.
    DivisionByZero,

    /// Inexact division where exact division was expected.
    InexactDivision,

    /// Inputs not coprime when they were expected to be coprime.
    InputsNotCoprime,
}

// See https://doc.rust-lang.org/std/marker/struct.PhantomData.html#ownership-and-the-drop-check
// for recommendations regarding phantom types. Note that we disregard the suggestion to use a
// const reference in the phantom type parameter, which causes issues for the `Send` trait.
#[derive(Debug, Eq, Hash, PartialEq)]
/// A cryptographic accumulator. Wraps a single unknown-order group element and phantom data
/// representing the type `T` being hashed-to-prime and accumulated.
pub struct Accumulator<G: UnknownOrderGroup, T> {
    pub(crate) phantom: PhantomData<T>,
    pub(crate) value: G::Elem,
}

impl<G: UnknownOrderGroup, T: Hash + Clone> Codec for Accumulator<G, T> {
    fn to_bytes(&self) -> Vec<u8> {
        self.value.to_bytes()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        Ok(Self {
            phantom: PhantomData,
            value: G::Elem::from_bytes(bytes)?,
        })
    }
}

// Manual clone impl required because Rust's type inference is not good. See
// https://github.com/rust-lang/rust/issues/26925.
impl<G: UnknownOrderGroup, T: Hash + Clone> Clone for Accumulator<G, T> {
    fn clone(&self) -> Self {
        Self {
            phantom: PhantomData,
            value: self.value.clone(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// A witness to one or more values in an accumulator, represented as an accumulator.
pub struct Witness<G: UnknownOrderGroup, T: Hash + Clone>(pub Accumulator<G, T>);

impl<G: UnknownOrderGroup, T: Hash + Clone + Eq + Sync + Send> Witness<G, T> {
    /// Empty accumulator
    pub fn empty() -> Self {
        Self(Accumulator::<G, T>::empty())
    }
}

impl<G: UnknownOrderGroup, T: Hash + Clone> Codec for Witness<G, T> {
    fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        Ok(Self(Accumulator::from_bytes(bytes)?))
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// Proof of correctness for accumulator updates
pub struct ProofOfCorrectness<G: UnknownOrderGroup, T: Hash + Clone> {
    /// Proof added
    pub proof_added: MembershipProof<G, T>,

    /// Proof deleted
    pub proof_deleted: MembershipProof<G, T>,
}

impl<G: UnknownOrderGroup, T: Hash + Clone> ProofOfCorrectness<G, T> {
    /// New proof of correctness
    pub fn new(proof_added: MembershipProof<G, T>, proof_deleted: MembershipProof<G, T>) -> Self {
        Self {
            proof_added,
            proof_deleted,
        }
    }

    /// Serialize to bytes
    pub fn to_bytes(&self) -> Vec<u8> {
        match (
            &self.proof_added.proof,
            &self.proof_deleted.proof,
            &self.proof_added.witness,
            &self.proof_deleted.witness,
        ) {
            (added_proof, deleted_proof, added_witness, deleted_witness)
                if added_proof == deleted_proof
                    && deleted_proof.Q == added_witness.0.value
                    && added_witness.0.value == deleted_witness.0.value =>
            {
                let mut buf = vec![0x00];
                buf.extend(self.proof_added.witness.to_bytes());
                buf
            }

            (added_proof, deleted_proof, added_witness, deleted_witness)
                if added_proof == deleted_proof
                    && added_witness.0.value == deleted_witness.0.value =>
            {
                let mut buf = vec![0x01];
                let witness_bytes = self.proof_added.witness.to_bytes();
                let proof_bytes = self.proof_added.proof.to_bytes();
                buf.extend_from_slice(&(witness_bytes.len() as u16).to_le_bytes());
                buf.extend_from_slice(&(proof_bytes.len() as u16).to_le_bytes());
                buf.extend(witness_bytes);
                buf.extend(proof_bytes);
                buf
            }

            (added_proof, deleted_proof, added_witness, deleted_witness)
                if added_proof != deleted_proof
                    && deleted_proof.Q == added_witness.0.value
                    && added_witness.0.value == deleted_witness.0.value =>
            {
                let mut buf = vec![0x02];
                let witness_bytes = self.proof_added.witness.to_bytes();
                let proof_bytes = self.proof_added.proof.to_bytes();
                buf.extend_from_slice(&(witness_bytes.len() as u16).to_le_bytes());
                buf.extend_from_slice(&(proof_bytes.len() as u16).to_le_bytes());
                buf.extend(witness_bytes);
                buf.extend(proof_bytes);
                buf
            }

            (added_proof, deleted_proof, added_witness, deleted_witness)
                if added_proof != deleted_proof
                    && added_proof.Q == added_witness.0.value
                    && added_witness.0.value == deleted_witness.0.value =>
            {
                let mut buf = vec![0x03];
                let witness_bytes = self.proof_added.witness.to_bytes();
                let proof_bytes = self.proof_deleted.proof.to_bytes();
                buf.extend_from_slice(&(witness_bytes.len() as u16).to_le_bytes());
                buf.extend_from_slice(&(proof_bytes.len() as u16).to_le_bytes());
                buf.extend(witness_bytes);
                buf.extend(proof_bytes);
                buf
            }

            (added_proof, deleted_proof, added_witness, deleted_witness)
                if added_proof != deleted_proof
                    && added_witness.0.value == deleted_witness.0.value =>
            {
                let mut buf = vec![0x04];
                let witness_bytes = self.proof_added.witness.to_bytes();
                let proof1_bytes = self.proof_added.proof.to_bytes();
                let proof2_bytes = self.proof_deleted.proof.to_bytes();
                buf.extend_from_slice(&(witness_bytes.len() as u16).to_le_bytes());
                buf.extend_from_slice(&(proof1_bytes.len() as u16).to_le_bytes());
                buf.extend_from_slice(&(proof2_bytes.len() as u16).to_le_bytes());
                buf.extend(witness_bytes);
                buf.extend(proof1_bytes);
                buf.extend(proof2_bytes);
                buf
            }

            _ => unreachable!(),
        }
    }

    /// Deserialize from bytes
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        if bytes.is_empty() {
            return Err("empty bytes received");
        }

        let rest = &bytes[1..];

        match bytes[0] {
            0x00 => {
                if rest.len() < 2 {
                    return Err("invalid bytes received");
                }

                let witness = Witness::from_bytes(rest)?;
                let qref: &G::Elem = &witness.0.value;
                let q: G::Elem = qref.clone();
                let proof_added = MembershipProof {
                    witness: witness.clone(),
                    proof: Poe::<G> { Q: q.clone() },
                };

                let proof_deleted = MembershipProof {
                    witness,
                    proof: Poe::<G> { Q: q },
                };

                Ok(Self {
                    proof_added,
                    proof_deleted,
                })
            }

            0x01 => {
                if rest.len() < 4 {
                    return Err("invalid bytes received");
                }

                let witness_bytes_len = &rest[..2];
                let proof_bytes_len = &rest[2..4];
                let mut l1 = [0; 2];
                let mut l2 = [0; 2];
                l1.copy_from_slice(witness_bytes_len);
                l2.copy_from_slice(proof_bytes_len);
                let len1 = u16::from_le_bytes(l1) as usize;
                let len2 = u16::from_le_bytes(l2) as usize;

                if rest[4..].len() != len1 + len2 {
                    return Err("invalid bytes len");
                }

                let witness = Witness::from_bytes(&rest[4..4 + len1])?;
                let proof = Poe::from_bytes(&rest[4 + len1..4 + len1 + len2])?;
                let proof_added = MembershipProof {
                    witness: witness.clone(),
                    proof: proof.clone(),
                };

                let proof_deleted = MembershipProof { witness, proof };

                Ok(Self {
                    proof_added,
                    proof_deleted,
                })
            }

            0x02 => {
                if rest.len() < 4 {
                    return Err("invalid bytes received");
                }

                let witness_bytes_len = &rest[..2];
                let proof_bytes_len = &rest[2..4];
                let mut l1 = [0; 2];
                let mut l2 = [0; 2];
                l1.copy_from_slice(witness_bytes_len);
                l2.copy_from_slice(proof_bytes_len);
                let len1 = u16::from_le_bytes(l1) as usize;
                let len2 = u16::from_le_bytes(l2) as usize;

                if rest[4..].len() != len1 + len2 {
                    return Err("invalid bytes len");
                }

                let witness = Witness::from_bytes(&rest[4..4 + len1])?;
                let proof = Poe::from_bytes(&rest[4 + len1..4 + len1 + len2])?;
                let qref: &G::Elem = &witness.0.value;
                let q: G::Elem = qref.clone();
                let proof_added = MembershipProof {
                    witness: witness.clone(),
                    proof,
                };

                let proof_deleted = MembershipProof {
                    witness,
                    proof: Poe::<G> { Q: q },
                };

                Ok(Self {
                    proof_added,
                    proof_deleted,
                })
            }

            0x03 => {
                if rest.len() < 4 {
                    return Err("invalid bytes received");
                }

                let witness_bytes_len = &rest[..2];
                let proof_bytes_len = &rest[2..4];
                let mut l1 = [0; 2];
                let mut l2 = [0; 2];
                l1.copy_from_slice(witness_bytes_len);
                l2.copy_from_slice(proof_bytes_len);
                let len1 = u16::from_le_bytes(l1) as usize;
                let len2 = u16::from_le_bytes(l2) as usize;

                if rest[4..].len() != len1 + len2 {
                    return Err("invalid bytes len");
                }

                let witness = Witness::from_bytes(&rest[4..4 + len1])?;
                let proof = Poe::from_bytes(&rest[4 + len1..4 + len1 + len2])?;
                let qref: &G::Elem = &witness.0.value;
                let q: G::Elem = qref.clone();
                let proof_deleted = MembershipProof {
                    witness: witness.clone(),
                    proof,
                };

                let proof_added = MembershipProof {
                    witness,
                    proof: Poe::<G> { Q: q },
                };

                Ok(Self {
                    proof_added,
                    proof_deleted,
                })
            }

            0x04 => {
                if rest.len() < 6 {
                    return Err("invalid bytes received");
                }

                let witness_bytes_len = &rest[..2];
                let proof1_bytes_len = &rest[2..4];
                let proof2_bytes_len = &rest[4..6];
                let mut l1 = [0; 2];
                let mut l2 = [0; 2];
                let mut l3 = [0; 2];
                l1.copy_from_slice(witness_bytes_len);
                l2.copy_from_slice(proof1_bytes_len);
                l3.copy_from_slice(proof2_bytes_len);
                let len1 = u16::from_le_bytes(l1) as usize;
                let len2 = u16::from_le_bytes(l2) as usize;
                let len3 = u16::from_le_bytes(l3) as usize;

                if rest[6..].len() != len1 + len2 + len3 {
                    return Err("invalid bytes len");
                }

                let witness = Witness::from_bytes(&rest[6..6 + len1])?;
                let proof1 = Poe::from_bytes(&rest[6 + len1..6 + len1 + len2])?;
                let proof2 = Poe::from_bytes(&rest[6 + len1 + len2..6 + len1 + len2 + len3])?;
                let proof_added = MembershipProof {
                    witness: witness.clone(),
                    proof: proof1,
                };

                let proof_deleted = MembershipProof {
                    witness,
                    proof: proof2,
                };

                Ok(Self {
                    proof_added,
                    proof_deleted,
                })
            }

            _ => Err("bad format"),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// A succinct proof of membership (some element is in some accumulator).
pub struct MembershipProof<G: UnknownOrderGroup, T: Hash + Clone> {
    /// The witness for the element in question.
    pub witness: Witness<G, T>,
    proof: Poe<G>,
}

impl<G: UnknownOrderGroup, T: Hash + Clone> Codec for MembershipProof<G, T> {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![];
        let wbytes = self.witness.to_bytes();
        let pbytes = self.proof.to_bytes();
        out.extend((wbytes.len() as u16).to_le_bytes());
        out.extend((pbytes.len() as u16).to_le_bytes());
        out.extend(wbytes);
        out.extend(pbytes);
        out
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        if bytes.len() < 4 {
            return Err("invalid bytes len");
        }

        let mut l1 = [0; 2];
        let mut l2 = [0; 2];
        l1.copy_from_slice(&bytes[..2]);
        l2.copy_from_slice(&bytes[2..4]);
        let len1 = u16::from_le_bytes(l1) as usize;
        let len2 = u16::from_le_bytes(l2) as usize;

        if bytes.len() != len1 + len2 + 4 || len1 == 0 || len2 == 0 {
            return Err("invalid bytes len");
        }

        let wbytes = &bytes[4..len1 + 4];
        let pbytes = &bytes[len1 + 4..len1 + 4 + len2];

        Ok(Self {
            witness: Witness::from_bytes(wbytes)?,
            proof: Poe::from_bytes(pbytes)?,
        })
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
/// A succinct proof of nonmembership (some element is not in some accumulator).
pub struct NonmembershipProof<G: UnknownOrderGroup, T: Sync> {
    phantom: PhantomData<*const T>,
    d: G::Elem,
    v: G::Elem,
    gv_inv: G::Elem,
    poke2_proof: Poke2<G>,
    poe_proof: Poe<G>,
}

impl<G: UnknownOrderGroup, T: Eq + Hash + Clone + Send + Sync> Accumulator<G, T> {
    /// Returns a new, empty accumulator.
    pub fn empty() -> Self {
        Self {
            phantom: PhantomData,
            value: G::unknown_order_elem(),
        }
    }

    /// Internal add method that also returns the prime hash product of added elements, enabling an
    /// efficient `add_with_proof`.
    fn add_(&self, elems: &[T]) -> (Self, Integer) {
        let x = prime_hash_product(elems);
        let acc_elem = G::exp(&self.value, &x);
        (
            Self {
                phantom: PhantomData,
                value: acc_elem,
            },
            x,
        )
    }

    // The conciseness of `accumulator.add()` and low probability of confusion with implementations of
    // the `Add` trait probably justify this...
    #[allow(clippy::should_implement_trait)]
    /// Adds `elems` to the accumulator. This cannot check whether the elements have already been
    /// added, so is up to clients to ensure uniqueness.
    ///
    /// Uses a move instead of a `&self` reference to prevent accidental use of the old accumulator.
    pub fn add(self, elems: &[T]) -> Self {
        self.add_(elems).0
    }

    /// A specialized version of `add` that also returns a batch membership proof for added elements.
    pub fn add_with_proof(self, elems: &[T]) -> (Self, MembershipProof<G, T>) {
        let (acc, x) = self.add_(elems);
        let proof = Poe::<G>::prove(&self.value, &x, &acc.value);
        (
            acc,
            MembershipProof {
                witness: Witness(self),
                proof,
            },
        )
    }

    /// Internal delete method that also returns the prime hash product of deleted elements, enabling
    /// an efficient `delete_with_proof`.
    ///
    /// Uses a divide-and-conquer approach to running the ShamirTrick, which keeps the average input
    /// smaller: For `[a, b, c, d]` do `S(S(a, b), S(c, d))` instead of `S(S(S(a, b), c), d)`.
    fn delete_(self, elem_witnesses: &[(T, Witness<G, T>)]) -> Result<(Self, Integer), AccError> {
        let prime_witnesses = elem_witnesses
            .par_iter()
            .map(|(elem, witness)| (hash_to_prime(elem), witness.0.value.clone()))
            .collect::<Vec<_>>();

        #[cfg(debug_assertions)]
        for (p, witness_elem) in &prime_witnesses {
            if G::exp(witness_elem, p) != self.value {
                return Err(AccError::BadWitness);
            }
        }

        let (prime_product, acc_elem) =
            divide_and_conquer::<G, _>((int(1), self.value), &prime_witnesses[..])?;

        Ok((
            Self {
                phantom: PhantomData,
                value: acc_elem,
            },
            prime_product,
        ))
    }

    /// Removes the elements in `elem_witnesses` from the accumulator.
    ///
    /// # Arguments
    ///
    /// * `elem_witnesses` - Tuples consisting of (element to delete, element's witness).
    ///
    /// Uses a move instead of a `&self` reference to prevent accidental use of the old accumulator.
    pub fn delete(self, elem_witnesses: &[(T, Witness<G, T>)]) -> Result<Self, AccError> {
        Ok(self.delete_(elem_witnesses)?.0)
    }

    /// A specialized version of `delete` that also returns a batch membership proof for deleted
    /// elements.
    pub fn delete_with_proof(
        self,
        elem_witnesses: &[(T, Witness<G, T>)],
    ) -> Result<(Self, MembershipProof<G, T>), AccError> {
        let (acc, prime_product) = self.clone().delete_(elem_witnesses)?;
        let proof = Poe::<G>::prove(&acc.value, &prime_product, &self.value);
        Ok((
            acc.clone(),
            MembershipProof {
                witness: Witness(acc),
                proof,
            },
        ))
    }

    /// Computes the batch membership proof for the elements in `elem_witnesses` w.r.t this
    /// accumulator.
    ///
    /// # Arguments
    ///
    /// * `elem_witnesses` - Tuples consisting of (element to prove, element's witness).
    pub fn prove_membership(
        &self,
        elem_witnesses: &[(T, Witness<G, T>)],
    ) -> Result<MembershipProof<G, T>, AccError> {
        let (witness_accum, prod) = rayon::join(
            || self.clone().delete(elem_witnesses),
            || {
                elem_witnesses
                    .par_iter()
                    .map(|(t, _)| hash_to_prime(t))
                    .product()
            },
        );
        let witness_accum = witness_accum?;
        let proof = Poe::<G>::prove(&witness_accum.value, &prod, &self.value);
        Ok(MembershipProof {
            witness: Witness(witness_accum),
            proof,
        })
    }

    /// Verifies a membership proof against the current accumulator and an element `t` whose
    /// inclusion is being proven.
    pub fn verify_membership(
        &self,
        t: &T,
        MembershipProof { witness, proof }: &MembershipProof<G, T>,
    ) -> bool {
        let exp = hash_to_prime(t);
        Poe::verify(&witness.0.value, &exp, &self.value, proof)
    }

    /// Verify membership proof but with an already hashed prime. Doesn't check if the element
    /// correctly hashes to a a prime.
    pub fn verify_membership_with_prime(
        &self,
        exp: &Integer,
        MembershipProof { witness, proof }: &MembershipProof<G, T>,
    ) -> bool {
        Poe::verify(&witness.0.value, &exp, &self.value, proof)
    }

    /// Batch version of `verify_membership` for multiple `elems`.
    pub fn verify_membership_batch(
        &self,
        elems: &[T],
        MembershipProof { witness, proof }: &MembershipProof<G, T>,
    ) -> bool {
        let exp = prime_hash_product(elems);
        Poe::verify(&witness.0.value, &exp, &self.value, proof)
    }

    /// Updates a `witness` for `tracked_elems` w.r.t the current accumulator, adding the elements in
    /// `untracked_additions` to the tracked set and removing the elements in `untracked_deletions`
    /// from the tracked set.
    ///
    /// See Section 4.2 of LLX for implementation details.
    pub fn update_membership_witness(
        &self,
        witness: Witness<G, T>,
        tracked_elems: &[T],
        untracked_additions: &[T],
        untracked_deletions: &[T],
    ) -> Result<Witness<G, T>, AccError> {
        let (x, x_hat) = rayon::join(
            || prime_hash_product(tracked_elems),
            || prime_hash_product(untracked_deletions),
        );

        #[cfg(debug_assertions)]
        for elem in tracked_elems {
            if untracked_additions.contains(elem) || untracked_deletions.contains(elem) {
                return Err(AccError::BadWitnessUpdate);
            }
        }

        let (gcd, a, b) = <(Integer, Integer, Integer)>::from(x.extended_gcd_ref(&x_hat));
        debug_assert!(gcd == int(1));

        let w = witness.0.add(untracked_additions);
        let (w_to_b, acc_new_to_a) =
            rayon::join(|| G::exp(&w.value, &b), || G::exp(&self.value, &a));
        Ok(Witness(Self {
            phantom: PhantomData,
            value: G::op(&w_to_b, &acc_new_to_a),
        }))
    }

    /// Computes the batch non-membership proof for the elements in `elems` w.r.t this accumulator
    /// and its `acc_set`.
    ///
    /// # Arguments
    ///
    /// * `acc_set` - The set of elements committed to by this accumulator.
    /// * `elems` - The set of elements you want to prove are not in `acc_set`.
    pub fn prove_nonmembership(
        &self,
        acc_set: &[T],
        elems: &[T],
    ) -> Result<NonmembershipProof<G, T>, AccError> {
        let x: Integer = elems.par_iter().map(hash_to_prime).product();
        let s = acc_set.par_iter().map(hash_to_prime).product();
        let (gcd, a, b) = <(Integer, Integer, Integer)>::from(x.extended_gcd_ref(&s));

        if gcd != int(1) {
            return Err(AccError::InputsNotCoprime);
        }

        let g = G::unknown_order_elem();
        let d = G::exp(&g, &a);
        let v = G::exp(&self.value, &b);
        let gv_inv = G::op(&g, &G::inv(&v));

        let poke2_proof = Poke2::prove(&self.value, &b, &v);
        let poe_proof = Poe::prove(&d, &x, &gv_inv);
        Ok(NonmembershipProof {
            phantom: PhantomData,
            d,
            v,
            gv_inv,
            poke2_proof,
            poe_proof,
        })
    }

    /// Verifies a non-membership proof against the current accumulator and elements `elems` whose
    /// non-inclusion is being proven.
    pub fn verify_nonmembership(
        &self,
        elems: &[T],
        NonmembershipProof {
            d,
            v,
            gv_inv,
            poke2_proof,
            poe_proof,
            ..
        }: &NonmembershipProof<G, T>,
    ) -> bool {
        let x = elems.par_iter().map(hash_to_prime).product();
        Poke2::verify(&self.value, v, poke2_proof) && Poe::verify(d, &x, gv_inv, poe_proof)
    }
}

impl<G: UnknownOrderGroup, T: Eq + Hash + Clone + Sync + Send> From<&[T]> for Accumulator<G, T> {
    fn from(ts: &[T]) -> Self {
        Self::empty().add(ts)
    }
}

impl<G: UnknownOrderGroup, T: Clone + Hash + Sync + Send + Eq> Witness<G, T> {
    /// Given a witness for `witness_set`, returns a witness for `witness_subset`.
    ///
    /// The `witness_subset` must be a subset of the `witness_set`.
    pub fn compute_subset_witness(
        self,
        witness_set: &[T],
        witness_subset: &[T],
    ) -> Result<Self, AccError>
    where
        T: PartialEq,
    {
        #[cfg(debug_assertions)]
        for witness in witness_subset {
            if !witness_set.contains(witness) {
                return Err(AccError::BadWitness);
            }
        }

        let (numerator, denominator) = rayon::join(
            || prime_hash_product(witness_set),
            || prime_hash_product(witness_subset),
        );
        let (quotient, remainder) = numerator.div_rem(denominator);

        if remainder != int(0) {
            return Err(AccError::InexactDivision);
        }

        Ok(Self(Accumulator {
            phantom: PhantomData,
            value: G::exp(&self.0.value, &quotient),
        }))
    }

    /// Given a witness for many `elems`, computes a sub-witness for each individual element in
    /// O(N log N) time.
    pub fn compute_individual_witnesses(&self, elems: &[T]) -> Vec<(T, Self)> {
        let hashes = elems.par_iter().map(hash_to_prime).collect::<Vec<_>>();
        elems
            .iter()
            .zip(self.root_factor(&hashes).iter())
            .map(|(x, y)| (x.clone(), y.clone()))
            .collect()
    }

    #[allow(non_snake_case)]
    fn root_factor(&self, elems: &[Integer]) -> Vec<Self> {
        if elems.len() == 1 {
            return vec![self.clone()];
        }
        let half_n = elems.len() >> 1;
        let cl1 = || {
            elems[..half_n].iter().fold(self.clone(), |sum, x| {
                Self(Accumulator {
                    phantom: PhantomData,
                    value: G::exp(&sum.0.value, x),
                })
            })
        };

        let cl2 = || {
            elems[half_n..].iter().fold(self.clone(), |sum, x| {
                Self(Accumulator {
                    phantom: PhantomData,
                    value: G::exp(&sum.0.value, x),
                })
            })
        };

        let (g_l, g_r) = rayon::join(cl1, cl2);
        let (mut L, mut R) = rayon::join(
            || g_r.root_factor(&Vec::from(&elems[..half_n])),
            || g_l.root_factor(&Vec::from(&elems[half_n..])),
        );
        L.append(&mut R);
        L
    }

    // Attempt at parallelising the above
    // #[allow(non_snake_case)]
    // fn root_factor(&self, elems: &[Integer]) -> Vec<Self> {
    //   if elems.len() == 1 {
    //     return vec![self.clone()];
    //   }
    //   let half_n = elems.len() >> 1;
    //   let cl1 = || {
    //     let vals = &[&[self.0.value.to_integer()][..], &elems[..half_n]].concat();
    //     let res = vals.par_iter().cloned().reduce_with(|sum, x| {
    //       G::exp(&G::Elem::from(sum), &x).to_integer()
    //     });

    //     Self(Accumulator {
    //       phantom: PhantomData,
    //       value: G::Elem::from(res.unwrap().clone()),
    //     })
    //   };

    //   let cl2 = || {
    //     let vals = &[&[self.0.value.to_integer()][..], &elems[half_n..]].concat();
    //     let res = vals.par_iter().cloned().reduce_with(|sum, x| {
    //       G::exp(&G::Elem::from(sum), &x).to_integer()
    //     });

    //     Self(Accumulator {
    //       phantom: PhantomData,
    //       value: G::Elem::from(res.unwrap().clone()),
    //     })
    //   };

    //   let (g_l, g_r) = rayon::join(cl1, cl2);
    //   let (mut L, mut R) = rayon::join(|| g_r.root_factor(&Vec::from(&elems[..half_n])), || g_l.root_factor(&Vec::from(&elems[half_n..])));
    //   L.append(&mut R);
    //   L
    // }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::group::{ClassGroup, Rsa2048};

    fn new_acc<G: UnknownOrderGroup, T: Hash + Clone + Eq + Sync + Send>(
        data: &[T],
    ) -> Accumulator<G, T> {
        Accumulator::<G, T>::empty().add(data)
    }

    macro_rules! test_all_groups {
    ($test_func:ident, $func_name_rsa:ident, $func_name_class:ident, $($attr:meta)*) => {
      #[test]
      $(
        #[$attr]
      )*
      fn $func_name_rsa() {
        $test_func::<Rsa2048>();
      }

      #[test]
      $(
        #[$attr]
      )*
      fn $func_name_class() {
        $test_func::<ClassGroup>();
      }
    };
  }

    test_all_groups!(test_add, test_add_rsa2048, test_add_class,);
    fn test_add<G: UnknownOrderGroup>() {
        let acc = new_acc::<G, &'static str>(&["a", "b"]);
        let new_elems = ["c", "d"];
        let (acc_new, proof) = acc.add_with_proof(&new_elems);
        let acc_expected = G::exp(
            &G::unknown_order_elem(),
            &prime_hash_product(&["a", "b", "c", "d"]),
        );
        assert!(acc_new.value == acc_expected);
        assert!(acc_new.verify_membership_batch(&new_elems, &proof));
    }

    test_all_groups!(test_delete, test_delete_rsa2048, test_delete_class,);
    fn test_delete<G: UnknownOrderGroup>() {
        let acc_0 = new_acc::<G, &'static str>(&["a", "b"]);
        let (acc_1, c_proof) = acc_0.clone().add_with_proof(&["c"]);
        let (acc_2, proof) = acc_1
            .clone()
            .delete_with_proof(&[("c", c_proof.witness)])
            .expect("valid delete expected");
        assert!(acc_2 == acc_0);
        assert!(acc_1.verify_membership(&"c", &proof));
    }

    test_all_groups!(
        test_delete_empty,
        test_delete_empty_rsa2048,
        test_delete_empty_class,
    );
    fn test_delete_empty<G: UnknownOrderGroup>() {
        let acc = new_acc::<G, &'static str>(&["a", "b"]);
        let (acc_new, proof) = acc
            .clone()
            .delete_with_proof(&[])
            .expect("valid delete expected");
        assert!(acc_new == acc);
        assert!(acc.verify_membership_batch(&[], &proof));
    }

    test_all_groups!(
        test_delete_bad_witness,
        test_delete_bad_witness_rsa2048,
        test_delete_bad_witness_class,
        should_panic(expected = "BadWitness")
    );
    fn test_delete_bad_witness<G: UnknownOrderGroup>() {
        let acc = Accumulator::<G, &'static str>::empty();
        let a_witness = Witness(new_acc::<G, &'static str>(&["b", "c"]));
        let b_witness = Witness(new_acc::<G, &'static str>(&["a", "c"]));
        acc.delete(&[("a", a_witness), ("b", b_witness)]).unwrap();
    }

    test_all_groups!(
        test_update_membership_witness,
        test_update_membership_witness_rsa2048,
        test_update_membership_witness_class,
    );
    fn test_update_membership_witness<G: UnknownOrderGroup>() {
        let acc = new_acc::<G, &'static str>(&["a", "b", "c"]);
        let witness = Witness(new_acc::<G, &'static str>(&["c", "d"]));
        let witness_new = acc
            .update_membership_witness(witness, &["a"], &["b"], &["d"])
            .unwrap();
        assert!(witness_new.0.add(&["a"]) == acc);
    }

    test_all_groups!(
        test_update_membership_witness_failure,
        test_update_membership_witness_failure_rsa2048,
        test_update_membership_witness_failure_class,
        should_panic(expected = "BadWitnessUpdate")
    );
    fn test_update_membership_witness_failure<G: UnknownOrderGroup>() {
        let acc = new_acc::<G, &'static str>(&["a", "b", "c"]);
        let witness = Witness(new_acc::<G, &'static str>(&["c", "d"]));
        acc.update_membership_witness(witness, &["a"], &["b"], &["a"])
            .unwrap();
    }

    test_all_groups!(
        test_prove_nonmembership,
        test_prove_nonmembership_rsa2048,
        test_prove_nonmembership_class,
    );
    fn test_prove_nonmembership<G: UnknownOrderGroup>() {
        let acc_set = ["a", "b"];
        let acc = new_acc::<G, &'static str>(&acc_set);
        let non_members = ["c", "d"];
        let proof = acc
            .prove_nonmembership(&acc_set, &non_members)
            .expect("valid proof expected");
        assert!(acc.verify_nonmembership(&non_members, &proof));
    }

    test_all_groups!(
        test_compute_sub_witness,
        test_compute_sub_witness_rsa2048,
        test_compute_sub_witness_class,
    );
    fn test_compute_sub_witness<G: UnknownOrderGroup>() {
        let empty_witness = Witness(Accumulator::<G, &'static str>::empty());
        let sub_witness = empty_witness
            .compute_subset_witness(&["a", "b"], &["a"])
            .unwrap();
        let exp_quotient_expected = Witness(new_acc::<G, &'static str>(&["b"]));
        assert!(sub_witness == exp_quotient_expected);
    }

    test_all_groups!(
        test_compute_sub_witness_failure,
        test_compute_sub_witness_failure_rsa2048,
        test_compute_sub_witness_failure_class,
        should_panic(expected = "BadWitness")
    );
    fn test_compute_sub_witness_failure<G: UnknownOrderGroup>() {
        let empty_witness = Witness(Accumulator::<G, &'static str>::empty());
        empty_witness
            .compute_subset_witness(&["a", "b"], &["c"])
            .unwrap();
    }

    fn test_compute_individual_witnesses<G: UnknownOrderGroup>() {
        let acc = new_acc::<G, &'static str>(&["a", "b", "c"]);
        let witness_multiple = Witness(new_acc::<G, &'static str>(&["a"]));
        let witnesses = witness_multiple.compute_individual_witnesses(&["b", "c"]);
        for (elem, witness) in witnesses {
            assert_eq!(acc.value, G::exp(&witness.0.value, &hash_to_prime(elem)));
        }
    }

    #[test]
    fn test_compute_individual_witnesses_rsa2048() {
        // Class version takes too long for a unit test.
        test_compute_individual_witnesses::<Rsa2048>();
    }
}
