// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::Shard;
use crate::chain::ShardBackend;
use crate::consensus::{Money, BLOCK_HORIZON};
use crate::primitives::{Hash160, Hash256, Output, PublicKey, TxVerifyErr};
use crate::vm::internal::VmTerm;
use crate::vm::Script;
use accumulator::group::{Codec, Rsa2048};
use accumulator::Witness;
use bincode::{Decode, Encode};
use schnorrkel::{PublicKey as SchnorPK, Signature as SchnorSig};

#[derive(PartialEq, Debug, Clone)]
pub struct Input {
    /// Output. Is null if this is a coinbase input
    pub out: Option<Output>,

    /// Spending public key. Is null if no spending public key is required or if this is a coinbase input.
    /// Present in a coloured coinbase input.
    pub spending_pkey: Option<PublicKey>,

    /// Output witness. Is null if this is a coinbase input
    pub witness: Option<Witness<Rsa2048, Output>>,

    /// Spending script
    pub script: Script,

    /// Additional spend script for coloured outputs. Can be used to limit the ability to spend a particular token
    pub colour_script: Option<Script>,

    /// Spend script arguments
    pub script_args: Vec<VmTerm>,

    /// Colour spend script arguments
    pub colour_script_args: Option<Vec<VmTerm>>,

    /// Merkle spend proof of address + script hash if spend key is present
    ///
    /// Otherwise this is the merkle proof of a script hash
    pub spend_proof: Option<Vec<Hash160>>,

    /// Merkle colour spend proof of address + colour script hash.
    ///
    /// This is mutually exclusive with colour_proof_without_address
    pub colour_proof: Option<Vec<Hash160>>,

    /// Merkle colour spend proof of colour script hash.
    ///
    /// This is mutually exclusive with colour_proof
    pub colour_proof_without_address: Option<Vec<Hash160>>,

    /// Block height chosen by the coinbase emitter for coinbase idempotency. Without it,
    /// an attacker can replay the transaction and emit more coins than intended.
    ///
    /// Must be greater or equal to `current_height - BLOCK_HORIZON`.
    pub coloured_coinbase_block_height: Option<u64>,

    /// Input hash. Not serialised
    pub hash: Option<Hash256>,

    /// Input flags. Not serialised
    pub input_flags: InputFlags,
}

impl Default for Input {
    fn default() -> Self {
        Self {
            out: None,
            spending_pkey: None,
            witness: None,
            script: Script::default(),
            colour_script: None,
            script_args: vec![],
            colour_script_args: None,
            spend_proof: None,
            colour_proof: None,
            colour_proof_without_address: None,
            coloured_coinbase_block_height: None,
            hash: None,
            input_flags: InputFlags::IsCoinbase,
        }
    }
}

impl Input {
    /// Serialize to bytes
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    /// Serializes to bytes for signing. Will not encode any script args or the out witness
    #[must_use]
    pub fn to_bytes_for_signing(&self) -> Vec<u8> {
        let mut copied = self.clone();

        // We don't sign the witness as it can be recomputed by miners
        copied.witness = None;

        // We also don't sign the script arguments marked as malleable
        let mut i = 0;
        while i < copied.script_args.len() {
            if copied.script.malleable_args[i] {
                copied.script_args.remove(i);
            } else {
                i += 1;
            }
        }

        crate::codec::encode_to_vec(&copied).unwrap()
    }

    pub fn compute_hash(&mut self, key: &str) {
        if self.hash.is_some() {
            return;
        }

        let bytes = self.to_bytes();
        self.hash = Some(Hash256::hash_from_slice(bytes, key));
    }

    #[must_use]
    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    #[must_use]
    pub fn out(&self) -> Option<&Output> {
        self.out.as_ref()
    }

    #[must_use]
    pub fn is_coinbase(&self) -> bool {
        self.out.is_none()
    }

    #[must_use]
    pub fn is_coloured(&self) -> bool {
        self.colour_script.is_some()
    }

    pub fn verify<'a, B: ShardBackend>(
        &'a self,
        height: u64,
        sum: &mut Money,
        transcripts: &mut Vec<&'a [u8]>,
        public_keys: &mut Vec<SchnorPK>,
        shard: &Shard<B>,
    ) -> Result<(), TxVerifyErr> {
        if self.is_coinbase() {
            let out_height = self.out.as_ref().unwrap().coinbase_height().unwrap();

            if height < out_height + BLOCK_HORIZON {
                return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
            }
        }

        let key = shard.shard_config().key();

        // Get script hash according to spend proof, address and script hash
        let oracle_script_hash = if let Some(ref spend_proof) = self.spend_proof {
            let mut out = self.script.to_script_hash(key);
            out.0 = Hash160::hash_from_slice(
                [
                    &self.spending_pkey.as_ref().unwrap().0.to_bytes(),
                    out.0.as_slice(),
                ]
                .concat(),
                key,
            )
            .0;

            for l in spend_proof {
                let l1 = out.0.as_ref();
                let l2 = l.0.as_ref();

                if l1 < l2 {
                    out.0 = Hash160::hash_from_slice(&[l1, l2].concat(), key).0;
                } else {
                    out.0 = Hash160::hash_from_slice(&[l2, l1].concat(), key).0;
                }
            }

            out
        } else {
            self.script.to_script_hash(key)
        };

        // Verify script hash
        if oracle_script_hash != self.out().unwrap().script_hash {
            return Err(TxVerifyErr::InvalidScriptHash);
        }

        *sum += self.out().unwrap().amount();
        transcripts.push(self.out().unwrap().hash().unwrap().as_bytes());
        if let Some(ref public_key) = self.spending_pkey {
            public_keys.push(public_key.0);
        }
        Ok(())
    }
}

impl Encode for Input {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        let flags = self.input_flags;
        let flags_to_write: u8 = flags as u8;
        bincode::Encode::encode(&flags_to_write, encoder)?;

        match flags {
            InputFlags::IsCoinbase => {
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::IsColouredCoinbase => {
                bincode::Encode::encode(self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(
                    &self.coloured_coinbase_block_height.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::Plain => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.witness.as_ref().unwrap().to_bytes(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
            }

            InputFlags::HasSpendProof => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.witness.as_ref().unwrap().to_bytes(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
            }

            InputFlags::HasSpendProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColoured => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProof => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProof => {
                unimplemented!()
            }

            InputFlags::PlainWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProof => {
                unimplemented!()
            }

            InputFlags::HasSpendProof => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProofWithoutAddress => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutAddress => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProofWithoutAddressWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey => {
                unimplemented!()
            }
        }

        Ok(())
    }
}

impl Decode for Input {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let input_flags: u8 = bincode::Decode::decode(decoder)?;
        let input_flags: InputFlags = input_flags.try_into().map_err(|err: &'static str| {
            bincode::error::DecodeError::OtherString(err.to_owned())
        })?;

        match input_flags {
            InputFlags::IsCoinbase => {
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    ..Default::default()
                })
            }

            InputFlags::IsColouredCoinbase => {
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let coloured_coinbase_block_height = Some(bincode::Decode::decode(decoder)?);
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    coloured_coinbase_block_height,
                    ..Default::default()
                })
            }

            InputFlags::Plain => {
                let out = Some(bincode::Decode::decode(decoder)?);
                let spending_pkey = Some(bincode::Decode::decode(decoder)?);
                let witness = {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    Some(
                        Witness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    )
                };
                let script = bincode::Decode::decode(decoder)?;
                let script_args: Vec<_> = bincode::Decode::decode(decoder)?;
                validate_script_args_len_during_decode(&script, script_args.as_slice())?;

                Ok(Self {
                    script,
                    script_args,
                    input_flags,
                    spending_pkey,
                    witness,
                    out,
                    ..Default::default()
                })
            }

            InputFlags::HasSpendProof => {
                unimplemented!()
            }

            InputFlags::HasSpendProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColoured => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProof => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProof => {
                unimplemented!()
            }

            InputFlags::PlainWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProof => {
                unimplemented!()
            }

            InputFlags::HasSpendProof => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProofWithoutAddress => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutAddress => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasColourProofWithoutAddressWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutSpendKey => {
                unimplemented!()
            }

            InputFlags::IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey => {
                unimplemented!()
            }
        }
    }
}

fn validate_script_args_len_during_decode(
    script: &Script,
    script_args: &[VmTerm],
) -> Result<(), bincode::error::DecodeError> {
    if script.malleable_args.len() != script_args.len() {
        return Err(bincode::error::DecodeError::OtherString(format!("Received more or fewer script arguments than the script requires. Expected: {}, Found: {}", script.malleable_args.len(), script_args.len())));
    }

    Ok(())
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum InputFlags {
    IsCoinbase = 0x00,
    IsColouredCoinbase = 0x01,
    Plain = 0x02,
    HasSpendProof = 0x03,
    IsColoured = 0x04,
    IsColouredHasColourProof = 0x05,
    IsColouredHasColourProofWithoutAddress = 0x06,
    IsColouredHasSpendProof = 0x07,
    IsColouredHasSpendProofAndColourProof = 0x08,
    IsColouredHasSpendProofAndColourProofWithoutAddress = 0x09,
    PlainWithoutSpendKey = 0x0a,
    HasSpendProofWithoutSpendKey = 0x0b,
    IsColouredWithoutSpendKey = 0x0c,
    IsColouredHasColourProofWithoutSpendKey = 0x0d,
    IsColouredHasColourProofWithoutAddressWithoutSpendKey = 0x1e,
    IsColouredHasSpendProofWithoutSpendKey = 0x0f,
    IsColouredHasSpendProofAndColourProofWithoutSpendKey = 0x10,
    IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey = 0x11,
}

impl std::convert::TryFrom<u8> for InputFlags {
    type Error = &'static str;

    fn try_from(num: u8) -> Result<Self, Self::Error> {
        match num {
            0x00 => Ok(Self::IsCoinbase),
            0x01 => Ok(Self::IsColouredCoinbase),
            0x02 => Ok(Self::Plain),
            0x03 => Ok(Self::HasSpendProof),
            0x04 => Ok(Self::IsColoured),
            0x05 => Ok(Self::IsColouredHasColourProof),
            0x06 => Ok(Self::IsColouredHasColourProofWithoutAddress),
            0x07 => Ok(Self::IsColouredHasSpendProof),
            0x08 => Ok(Self::IsColouredHasSpendProofAndColourProof),
            0x08 => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutAddress),
            0x0a => Ok(Self::PlainWithoutSpendKey),
            0x0b => Ok(Self::HasSpendProofWithoutSpendKey),
            0x0c => Ok(Self::IsColouredWithoutSpendKey),
            0x0d => Ok(Self::IsColouredHasColourProofWithoutSpendKey),
            0x0e => Ok(Self::IsColouredHasColourProofWithoutAddressWithoutSpendKey),
            0x0f => Ok(Self::IsColouredHasSpendProofWithoutSpendKey),
            0x10 => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutSpendKey),
            0x11 => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey),
            _ => Err("invalid bitflags"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::Address;

    #[test]
    fn coinbase_encode_decode() {
        let input = Input {
            script: Script::new_coinbase(),
            input_flags: InputFlags::IsCoinbase,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned64(1_654_654_645_645),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn coloured_coinbase_encode_decode() {
        let input = Input {
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_coinbase(),
            coloured_coinbase_block_height: Some(342),
            input_flags: InputFlags::IsColouredCoinbase,
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned64(1_654_654_645_645),
                VmTerm::Unsigned32(543_543),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }

    #[test]
    fn plain_encode_decode() {
        let input = Input {
            out: Some(Output {
                amount: 100,
                script_hash: Hash160::zero(),
                inputs_hash: Hash160::zero(),
                script_outs: vec![],
                idx: 0,
                address: Some(Address::zero()),
                coloured_address: None,
                coinbase_height: None,
                hash: None,
            }),
            witness: Some(Witness::empty()),
            input_flags: InputFlags::Plain,
            spending_pkey: Some(PublicKey::zero()),
            script: Script::new_simple_spend(),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
            ],
            ..Default::default()
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }
}
