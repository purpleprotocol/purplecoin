// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use ed25519_dalek::{
    verify_batch as verify_batch_ed25519, Signature as Ed25519Signature,
    SigningKey as Ed25519SigningKey, VerifyingKey as Ed25519VerifyingKey,
};
use itertools::izip;
use libsecp256k1::{verify as verify_ecdsa, Message, PublicKey, Signature};
use schnorrkel::{
    signing_context, verify_batch as verify_batch_schnor, PublicKey as SchnorPK,
    Signature as SchnorSig,
};
use secp256k1::schnorr::Signature as Bip340Signature;
use secp256k1::{Message as Secp256k1Message, Secp256k1, XOnlyPublicKey};

pub fn verify_single_schnor(
    ctx: &str,
    pub_key: &SigVerificationPubKey,
    sig: &SigVerificationSignature,
    message: &SigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    let ctx = signing_context(ctx.as_bytes());
    let pub_key = SchnorPK::from_bytes(pub_key.as_slice()).unwrap();
    let sig = SchnorSig::from_bytes(sig.as_slice()).unwrap();
    pub_key
        .verify(ctx.bytes(message), &sig)
        .map_err(|_| SigVerificationErr::InvalidSignature)
}

pub fn verify_single_ed25519(
    pub_key: &SigVerificationPubKey,
    sig: &SigVerificationSignature,
    message: &SigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    let mut ver_stack = VerificationStack::new();
    ver_stack.push_ed25519(
        message.clone(),
        sig.into(),
        Ed25519VerifyingKey::from_bytes(pub_key)
            .map_err(|_| SigVerificationErr::InvalidPublicKey)?,
    );
    ver_stack.ed25519.verify_batch()
}

pub fn verify_single_ecdsa(
    pub_key: &EcdsaPublicKey,
    sig: &SigVerificationSignature,
    message: &EcdsaSigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    let message = Message::parse(message);
    let mut sig = Signature::parse_standard(sig).map_err(|_| SigVerificationErr::EcdsaRecErr)?;
    let public_key =
        PublicKey::parse_compressed(pub_key).map_err(|_| SigVerificationErr::InvalidPublicKey)?;
    sig.normalize_s();
    if verify_ecdsa(&message, &sig, &public_key) {
        Ok(())
    } else {
        Err(SigVerificationErr::InvalidSignature)
    }
}

pub fn verify_single_bip340(
    pub_key: &SigVerificationPubKey,
    sig: &SigVerificationSignature,
    message: &EcdsaSigVerificationMessage,
) -> Result<(), SigVerificationErr> {
    let pub_key =
        XOnlyPublicKey::from_slice(pub_key).map_err(|_| SigVerificationErr::InvalidPublicKey)?;
    let signature =
        Bip340Signature::from_slice(sig).map_err(|_| SigVerificationErr::InvalidSignature)?;
    let message = Secp256k1Message::from_digest_slice(message)
        .map_err(|_| SigVerificationErr::InvalidMessage)?;
    let ctx = Secp256k1::new();
    ctx.verify_schnorr(&signature, &message, &pub_key)
        .map_err(|_| SigVerificationErr::InvalidSignature)
}

pub fn verify_batch(ver_stack: &VerificationStack) -> Result<(), SigVerificationErr> {
    // TODO: Bench and parallelise this finely for mainnet. Shortcircuiting needed.
    ver_stack.ed25519.verify_batch()?;
    ver_stack.ecdsa.verify_batch()?;
    ver_stack.bip340.verify_batch()?;
    Ok(())
}

#[derive(Default)]
pub struct VerificationStack {
    pub(crate) schnor: SchnorVerStack,
    pub(crate) ed25519: Ed25519VerStack,
    pub(crate) ecdsa: EcdsaVerStack,
    pub(crate) bip340: BIP340VerStack,
}

impl VerificationStack {
    #[must_use]
    pub fn new() -> Self {
        Default::default()
    }

    pub fn push_ed25519(
        &mut self,
        message: SigVerificationMessage,
        signature: Ed25519Signature,
        public_key: Ed25519VerifyingKey,
    ) {
        self.ed25519.transcripts.push(message);
        self.ed25519.signatures.push(signature);
        self.ed25519.public_keys.push(public_key);
    }

    pub fn push_ecdsa(
        &mut self,
        message: EcdsaSigVerificationMessage,
        signature: SigVerificationSignature,
        public_key: EcdsaPublicKey,
    ) {
        self.ecdsa.transcripts.push(message);
        self.ecdsa.signatures.push(signature);
        self.ecdsa.public_keys.push(public_key);
    }

    pub fn push_bip340(
        &mut self,
        message: EcdsaSigVerificationMessage,
        signature: SigVerificationSignature,
        public_key: Bip340PublicKey,
    ) {
        self.bip340.transcripts.push(message);
        self.bip340.signatures.push(signature);
        self.bip340.public_keys.push(public_key);
    }
}

#[derive(Default)]
pub(crate) struct SchnorVerStack {
    transcripts: Vec<SigVerificationMessage>,
    signatures: Vec<SchnorSig>,
    public_keys: Vec<SchnorPK>,
}

impl SchnorVerStack {
    pub fn verify_batch(&self) -> Result<(), SigVerificationErr> {
        unimplemented!();
    }
}

#[derive(Default)]
pub(crate) struct Ed25519VerStack {
    transcripts: Vec<SigVerificationMessage>,
    signatures: Vec<Ed25519Signature>,
    public_keys: Vec<Ed25519VerifyingKey>,
}

impl Ed25519VerStack {
    pub fn verify_batch(&self) -> Result<(), SigVerificationErr> {
        let messages: Vec<_> = self
            .transcripts
            .iter()
            .map(std::vec::Vec::as_slice)
            .collect();
        verify_batch_ed25519(&messages, &self.signatures, &self.public_keys)
            .map_err(|_| SigVerificationErr::InvalidSignature)
    }
}

#[derive(Default)]
pub(crate) struct EcdsaVerStack {
    transcripts: Vec<EcdsaSigVerificationMessage>,
    signatures: Vec<SigVerificationSignature>,
    public_keys: Vec<EcdsaPublicKey>,
}

impl EcdsaVerStack {
    pub fn verify_batch(&self) -> Result<(), SigVerificationErr> {
        // TODO: Bench and parallelise this finely for mainnet. Shortcircuiting needed.
        let mut counter = 0;
        let mut iter = izip!(
            self.transcripts.iter(),
            self.signatures.iter(),
            self.public_keys.iter()
        )
        .take_while(|(m, s, pk)| verify_single_ecdsa(pk, s, m).is_ok());

        for _ in iter {
            counter += 1;
        }

        if counter == self.transcripts.len() {
            Ok(())
        } else {
            Err(SigVerificationErr::InvalidSignature)
        }
    }
}

#[derive(Default)]
pub(crate) struct BIP340VerStack {
    transcripts: Vec<EcdsaSigVerificationMessage>,
    signatures: Vec<SigVerificationSignature>,
    public_keys: Vec<Bip340PublicKey>,
}

impl BIP340VerStack {
    pub fn verify_batch(&self) -> Result<(), SigVerificationErr> {
        // TODO: Bench and parallelise this finely for mainnet. Shortcircuiting needed.
        let mut counter = 0;
        let mut iter = izip!(
            self.transcripts.iter(),
            self.signatures.iter(),
            self.public_keys.iter()
        )
        .take_while(|(m, s, pk)| verify_single_bip340(pk, s, m).is_ok());

        for _ in iter {
            counter += 1;
        }

        if counter == self.transcripts.len() {
            Ok(())
        } else {
            Err(SigVerificationErr::InvalidSignature)
        }
    }
}

pub type SigVerificationPubKey = [u8; 32];
pub type SigVerificationSignature = [u8; 64];
pub type SigVerificationMessage = Vec<u8>;
pub type EcdsaSigVerificationMessage = [u8; 32];
pub type EcdsaPublicKey = [u8; 33];
pub type Bip340PublicKey = [u8; 32];

#[derive(Clone, Debug)]
pub enum SigVerificationErr {
    /// Invalid signature
    InvalidSignature,

    /// Invalid public key
    InvalidPublicKey,

    /// Invalid message in case of ECDSA usually
    /// because it's not 32 bytes long or not hashed
    /// with a cryptographic hash function.
    InvalidMessage,

    /// ECDSA public key recovery error
    EcdsaRecErr,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::Hash256;
    use ed25519_dalek::{Signer, SigningKey as Ed25519SigningKey};
    use libsecp256k1::*;
    use rand::rngs::OsRng;
    use secp256k1::Keypair;

    #[test]
    fn verify_ed25519() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..200_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let message = vec![i];
                let signing_key = Ed25519SigningKey::generate(&mut csprng);
                let pkey = signing_key.verifying_key();
                let signature = signing_key.sign(&message);
                (message, pkey, signature)
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_ed25519(message.clone(), signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_ok());
    }

    #[test]
    fn verify_ed25519_fail_case() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..200_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut message = vec![i];
                let signing_key = Ed25519SigningKey::generate(&mut csprng);
                let pkey = signing_key.verifying_key();
                let signature = signing_key.sign(&message);
                if i == 0 {
                    message = vec![0xff];
                }
                (message, pkey, signature)
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_ed25519(message.clone(), signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_err());
    }

    #[test]
    fn verify_ed25519_single() {
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let message = vec![i];
                let signing_key = Ed25519SigningKey::generate(&mut csprng);
                let pkey = signing_key.verifying_key();
                let signature = signing_key.sign(&message);
                (message, pkey, signature)
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            assert!(
                verify_single_ed25519(&pkey.to_bytes(), &signature.to_bytes(), &message).is_ok()
            );
        }
    }

    #[test]
    fn verify_ed25519_single_fail_case() {
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut message = vec![i];
                let signing_key = Ed25519SigningKey::generate(&mut csprng);
                let pkey = signing_key.verifying_key();
                let signature = signing_key.sign(&message);
                if i == 0 {
                    message = vec![0xff];
                }
                (message, pkey, signature)
            })
            .collect::<Vec<_>>();

        for (i, (message, pkey, signature)) in batch.iter().enumerate() {
            if i == 0 {
                assert!(
                    verify_single_ed25519(&pkey.to_bytes(), &signature.to_bytes(), message)
                        .is_err()
                );
            } else {
                assert!(
                    verify_single_ed25519(&pkey.to_bytes(), &signature.to_bytes(), message).is_ok()
                );
            }
        }
    }

    #[test]
    fn verify_ecdsa_single() {
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let signing_key = SecretKey::random(&mut csprng);
                let pkey = PublicKey::from_secret_key(&signing_key);
                let message = Message::parse(&m);
                let (signature, rec_id) = sign(&message, &signing_key);
                (m, pkey.serialize_compressed(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            assert!(verify_single_ecdsa(&pkey, &signature, &message).is_ok());
        }
    }

    #[test]
    fn verify_ecdsa_single_fail_case() {
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let signing_key = SecretKey::random(&mut csprng);
                let pkey = PublicKey::from_secret_key(&signing_key);
                let message = Message::parse(&m);
                let (signature, rec_id) = sign(&message, &signing_key);
                if i == 0 {
                    m = quick_sha256(vec![0xff].as_slice());
                }
                (m, pkey.serialize_compressed(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (i, (message, pkey, signature)) in batch.iter().enumerate() {
            if i == 0 {
                assert!(verify_single_ecdsa(pkey, signature, message).is_err());
            } else {
                assert!(verify_single_ecdsa(pkey, signature, message).is_ok());
            }
        }
    }

    #[test]
    fn verify_ecdsa_batch() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let signing_key = SecretKey::random(&mut csprng);
                let pkey = PublicKey::from_secret_key(&signing_key);
                let message = Message::parse(&m);
                let (signature, rec_id) = sign(&message, &signing_key);
                (m, pkey.serialize_compressed(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_ecdsa(message, signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_ok());
    }

    #[test]
    fn verify_ecdsa_batch_fail_case() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let signing_key = SecretKey::random(&mut csprng);
                let pkey = PublicKey::from_secret_key(&signing_key);
                let message = Message::parse(&m);
                let (signature, rec_id) = sign(&message, &signing_key);
                if i == 0 {
                    m = quick_sha256(vec![0xff].as_slice());
                }
                (m, pkey.serialize_compressed(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_ecdsa(message, signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_err());
    }

    #[test]
    fn verify_ecdsa_batch_fail_case_2() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let signing_key = SecretKey::random(&mut csprng);
                let pkey = PublicKey::from_secret_key(&signing_key);
                let message = Message::parse(&m);
                let (signature, rec_id) = sign(&message, &signing_key);
                if i == 47 {
                    m = quick_sha256(vec![0xff].as_slice());
                }
                (m, pkey.serialize_compressed(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_ecdsa(message, signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_err());
    }

    #[test]
    fn verify_bip340_batch() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let ctx = Secp256k1::new();
                let (signing_key, _) = ctx.generate_keypair(&mut csprng);
                let (pub_key, _) = signing_key.x_only_public_key(&ctx);
                let message = Secp256k1Message::from_digest_slice(&m).unwrap();
                let keypair = Keypair::from_secret_key(&ctx, &signing_key);
                let signature = ctx.sign_schnorr(&message, &keypair);
                (m, pub_key.serialize(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_bip340(message, signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_ok());
    }

    #[test]
    fn verify_bip340_batch_fail_case() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let ctx = Secp256k1::new();
                let (signing_key, _) = ctx.generate_keypair(&mut csprng);
                let (pub_key, _) = signing_key.x_only_public_key(&ctx);
                let message = Secp256k1Message::from_digest_slice(&m).unwrap();
                let keypair = Keypair::from_secret_key(&ctx, &signing_key);
                let signature = ctx.sign_schnorr(&message, &keypair);
                if i == 0 {
                    m = quick_sha256(vec![0xff].as_slice());
                }
                (m, pub_key.serialize(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_bip340(message, signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_err());
    }

    #[test]
    fn verify_bip340_batch_fail_case_2() {
        let mut ver_stack = VerificationStack::new();
        let batch = (0..50_u8)
            .map(|i| {
                let mut csprng = OsRng;
                let mut m = quick_sha256(vec![i].as_slice());
                let ctx = Secp256k1::new();
                let (signing_key, _) = ctx.generate_keypair(&mut csprng);
                let (pub_key, _) = signing_key.x_only_public_key(&ctx);
                let message = Secp256k1Message::from_digest_slice(&m).unwrap();
                let keypair = Keypair::from_secret_key(&ctx, &signing_key);
                let signature = ctx.sign_schnorr(&message, &keypair);
                if i == 47 {
                    m = quick_sha256(vec![0xff].as_slice());
                }
                (m, pub_key.serialize(), signature.serialize())
            })
            .collect::<Vec<_>>();

        for (message, pkey, signature) in batch {
            ver_stack.push_bip340(message, signature, pkey);
        }

        assert!(verify_batch(&ver_stack).is_err());
    }

    fn quick_sha256(bytes: &[u8]) -> [u8; 32] {
        use sha2::Digest;
        let mut hasher = sha2::Sha256::new();
        Digest::update(&mut hasher, bytes);
        let hashed_term = hasher.finalize();
        let mut out = [0; 32];
        out.copy_from_slice(&hashed_term[..]);
        out
    }
}
