// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

/// A sig verification enum for different signature schemes, to be used
/// for both batch and single verification, for vm verification.
pub enum SigVerification {
    Schnor(
        SigVerificationPubKey,
        SigVerificationSignature,
        SigVerificationMessage,
    ),
    Ed25519(
        SigVerificationPubKey,
        SigVerificationSignature,
        SigVerificationMessage,
    ),
    Ecdsa(
        SigVerificationSignature,
        SigVerificationMessage,
        EcdsaRecoveryId,
    ),
    BIP340(
        SigVerificationPubKey,
        SigVerificationSignature,
        SigVerificationMessage,
    ),
}

impl SigVerification {
    pub fn verify_single(&self) -> Result<(), SigVerificationErr> {
        unimplemented!()
    }
}

pub fn verify_batch(ver_stack: Vec<SigVerification>) -> Result<(), SigVerificationErr> {
    unimplemented!();
}

pub struct SigVerificationPubKey([u8; 32]);
pub struct SigVerificationSignature([u8; 64]);
pub type SigVerificationMessage = Vec<u8>;
pub type EcdsaRecoveryId = u8;

#[derive(Clone, Debug)]
pub enum SigVerificationErr {
    InvalidSignature,
}
