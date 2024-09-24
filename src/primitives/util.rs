// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2024 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use bitvec::prelude::*;

use super::{Hash160, PublicKey};
use crate::vm::{internal::VmTerm, Script};

/// Key used for hashing colour hashes
pub const COLOUR_HASH_KEY: &str = "purplecoin.hash.colour.20";

/// Returns a colour kernel hash. The colour kernel is the
/// spending pkey + non_malleable_script_args of the coloured coinbase input.
///
/// A colour kernel is hashed together with the hash of the emitting colour script,
/// to create the colour hash of an asset.
pub fn get_colour_kernel_hash(
    non_malleable_script_args: &[VmTerm],
    spending_pkey: &PublicKey,
) -> Hash160 {
    let mut buf = vec![];
    for a in non_malleable_script_args {
        buf.extend_from_slice(&a.to_bytes());
    }
    buf.extend_from_slice(&spending_pkey.to_bytes());
    Hash160::hash_from_slice(buf, COLOUR_HASH_KEY)
}

/// Compute a colour hash, based on a script, non malleable args,
/// and a spending pkey as such:
///
/// colour_hash = hash(hash(script) + hash(non_malleable_script_args + spending_key))
///
/// All hashing is done with the colour hashing key for global uniqueness.
///
/// Returns the colour hash and the colour kernel hash.
pub fn compute_colour_hash(
    script: &Script,
    non_malleable_script_args: &[VmTerm],
    spending_pkey: &PublicKey,
) -> (Hash160, Hash160) {
    let script_hash = script.to_script_hash(COLOUR_HASH_KEY);
    let colour_kernel_hash = get_colour_kernel_hash(non_malleable_script_args, spending_pkey);
    let buf = [&script_hash.0[..], &colour_kernel_hash.0[..]].concat();
    (
        Hash160::hash_from_slice(buf, COLOUR_HASH_KEY),
        colour_kernel_hash,
    )
}

/// Checks if a script matches the provided colour hash by hashing it against
/// the provided colour kernel.
pub fn validate_script_against_colour_hash(
    script: &Script,
    colour_hash: &Hash160,
    colour_kernel: &Hash160,
) -> bool {
    let script_hash = script.to_script_hash(COLOUR_HASH_KEY);
    let buf = [&script_hash.0[..], &colour_kernel.0[..]].concat();
    let computed_colour_hash = Hash160::hash_from_slice(buf, COLOUR_HASH_KEY);
    &computed_colour_hash == colour_hash
}

/// Filters the malleable script args from an arg vector based on the provided bitmap.
///
/// Returns `None` if the bitvec and the args vec don't have the same length.
pub fn get_non_malleable_script_args(args: &[VmTerm], bitvec: &BitVec) -> Option<Vec<VmTerm>> {
    if args.len() != bitvec.len() {
        return None;
    }

    let mut copied_args = args.to_vec();
    let mut i = 0;
    let mut r = 0;
    while i + r < bitvec.len() {
        if bitvec[i + r] {
            copied_args.remove(i);
            r += 1;
        } else {
            i += 1;
        }
    }

    Some(copied_args)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colour_kernel_hash_regression_1() {
        let kernel_hash = get_colour_kernel_hash(&[], &PublicKey::zero()).to_hex();
        assert_eq!(
            kernel_hash.as_str(),
            "ecf4362def33456eeca45951106983d16e35d5b8"
        );
    }

    #[test]
    fn colour_kernel_hash_regression_2() {
        let pkey = PublicKey::zero();
        let kernel_hash = get_colour_kernel_hash(
            &[
                VmTerm::Unsigned8(65),
                VmTerm::Unsigned64(438726),
                VmTerm::Unsigned8Array(vec![0x03, 0xe3, 0x45]),
            ],
            &pkey,
        )
        .to_hex();

        assert_eq!(
            kernel_hash.as_str(),
            "5622d429d883c9cf858598ab796420695fa91070"
        );
    }

    #[test]
    fn colour_hash_regression_1() {
        let script = Script::new_nop_script();
        let colour_hash = compute_colour_hash(&script, &[], &PublicKey::zero())
            .0
            .to_hex();
        assert_eq!(
            colour_hash.as_str(),
            "54e0bb86aba194058283144b98586d76b01c0fac"
        );
    }

    #[test]
    fn colour_hash_regression_2() {
        let script = Script::new_simple_spend();
        let colour_hash = compute_colour_hash(
            &script,
            &[
                VmTerm::Unsigned8(65),
                VmTerm::Unsigned64(438726),
                VmTerm::Unsigned8Array(vec![0x03, 0xe3, 0x45]),
            ],
            &PublicKey::zero(),
        )
        .0
        .to_hex();
        assert_eq!(
            colour_hash.as_str(),
            "3ffd79124eb32db05a85ea35f2e1ffd612a928d6"
        );
    }

    #[test]
    fn it_validates_script_against_colour_hash_1() {
        let script = Script::new_nop_script();
        let result = compute_colour_hash(&script, &[], &PublicKey::zero());
        assert!(validate_script_against_colour_hash(
            &script, &result.0, &result.1
        ));
    }

    #[test]
    fn it_validates_script_against_colour_hash_2() {
        let script = Script::new_simple_spend();
        let result = compute_colour_hash(
            &script,
            &[
                VmTerm::Unsigned8(65),
                VmTerm::Unsigned64(438726),
                VmTerm::Unsigned8Array(vec![0x03, 0xe3, 0x45]),
            ],
            &PublicKey::zero(),
        );
        assert!(validate_script_against_colour_hash(
            &script, &result.0, &result.1
        ));
    }

    #[test]
    fn it_validates_script_against_colour_hash_3() {
        let script = Script::new_simple_spend();
        let script2 = Script::new_nop_script();
        let result = compute_colour_hash(
            &script,
            &[
                VmTerm::Unsigned8(65),
                VmTerm::Unsigned64(438726),
                VmTerm::Unsigned8Array(vec![0x03, 0xe3, 0x45]),
            ],
            &PublicKey::zero(),
        );
        assert!(!validate_script_against_colour_hash(
            &script2, &result.0, &result.1
        ));
    }

    #[test]
    fn it_filters_malleable_script_args() {
        let args = vec![
            VmTerm::Unsigned8(65),
            VmTerm::Unsigned64(438726),
            VmTerm::Unsigned8Array(vec![0x03, 0xe3, 0x45]),
            VmTerm::Unsigned32(6543),
            VmTerm::Unsigned32(548937),
        ];
        let bv = bitvec![0, 1, 1, 0, 0];

        assert_eq!(
            get_non_malleable_script_args(&args, &bv).unwrap(),
            vec![
                VmTerm::Unsigned8(65),
                VmTerm::Unsigned32(6543),
                VmTerm::Unsigned32(548937),
            ]
        );
    }

    #[test]
    fn get_non_malleable_script_args_fails_when_args_differ_in_length() {
        let args = vec![
            VmTerm::Unsigned8(65),
            VmTerm::Unsigned64(438726),
            VmTerm::Unsigned8Array(vec![0x03, 0xe3, 0x45]),
            VmTerm::Unsigned32(6543),
            VmTerm::Unsigned32(548937),
        ];
        let bv = bitvec![0, 1, 1, 0];

        assert!(get_non_malleable_script_args(&args, &bv).is_none());
    }
}
