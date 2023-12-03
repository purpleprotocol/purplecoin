// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use ed25519_dalek::{
    verify_batch as verify_batch_ed25519, Signature as Ed25519Signature,
    SigningKey as Ed25519SigningKey, VerifyingKey as Ed25519VerifyingKey,
};
use schnorrkel::{
    signing_context, verify_batch as verify_batch_schnor, PublicKey as SchnorPK,
    Signature as SchnorSig,
};

pub fn verify_single_schnor(
    ctx: &str,
    pub_key: &SigVerificationPubKey,
    sig: &SigVerificationSignature,
    message: &SigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    unimplemented!();
}

pub fn verify_single_ed25519(
    pub_key: &SigVerificationPubKey,
    sig: &SigVerificationSignature,
    message: &SigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    unimplemented!();
}

pub fn verify_single_ecdsa(
    rec_id: &EcdsaRecoveryId,
    sig: &SigVerificationSignature,
    message: &SigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    unimplemented!();
}

pub fn verify_single_bip340(
    pub_key: &SigVerificationPubKey,
    sig: &SigVerificationSignature,
    message: &SigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    unimplemented!();
}

pub fn verify_batch(ver_stack: &VerificationStack) -> Result<(), SigVerificationErr> {
    unimplemented!();
}

#[derive(Default)]
pub struct VerificationStack {
    schnor: SchnorVerStack,
    ed25519: Ed25519VerStack,
    ecdsa: EcdsaVerStack,
    bip340: BIP340VerStack,
}

impl VerificationStack {
    #[must_use]
    pub fn new() -> Self {
        Default::default()
    }
}

#[derive(Default)]
struct SchnorVerStack {
    transcripts: Vec<SigVerificationMessage>,
    signatures: Vec<SchnorSig>,
    public_keys: Vec<SchnorPK>,
}

#[derive(Default)]
struct Ed25519VerStack {
    transcripts: Vec<SigVerificationMessage>,
    signatures: Vec<Ed25519Signature>,
    public_keys: Vec<Ed25519VerifyingKey>,
}

#[derive(Default)]
struct EcdsaVerStack {
    transcripts: Vec<SigVerificationMessage>,
    signatures: Vec<SigVerificationSignature>,
}

#[derive(Default)]
struct BIP340VerStack {
    transcripts: Vec<SigVerificationMessage>,
    signatures: Vec<SigVerificationSignature>,
    public_keys: Vec<SigVerificationPubKey>,
}

pub struct SigVerificationPubKey([u8; 32]);
pub struct SigVerificationSignature([u8; 64]);
pub type SigVerificationMessage = Vec<u8>;
pub type EcdsaRecoveryId = u8;

#[derive(Clone, Debug)]
pub enum SigVerificationErr {
    InvalidSignature,
}
