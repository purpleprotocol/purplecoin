// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::Shard;
use crate::chain::ShardBackend;
use crate::consensus::*;
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

    /// Spending public key. Is null if no spending public key is required or if this is a coinbase input
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

    /// Merkle colour spend proof of address + colour script hash. Usage with whitelisted spending public keys.
    ///
    /// This is mutually exclusive with colour_proof_without_address
    pub colour_proof: Option<Vec<Hash160>>,

    /// Merkle colour spend proof of colour script hash. Usage without whitelisted spending public keys
    ///
    /// This is mutually exclusive with colour_proof
    pub colour_proof_without_address: Option<Vec<Hash160>>,

    /// Sequence number. An input is considered final if this is equal to 0xffffffff
    pub nsequence: u32,

    /// Input hash. Not serialized
    pub hash: Option<Hash256>,
}

impl Input {
    /// Serialize to bytes
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    /// Serializes to bytes for signing. Will not encode any script args or the out witness
    pub fn to_bytes_for_signing(&self) -> Vec<u8> {
        let mut copied = self.clone();
        
        // We don't sign or hash the witness as it can be recomputed by miners 
        copied.witness = None; 

        // We also don't sign or hash the script arguments marked as malleable
        // unimplemented!();

        crate::codec::encode_to_vec(&copied).unwrap()
    }

    pub fn compute_hash(&mut self, key: &str) {
        if self.hash.is_some() {
            return;
        }

        let bytes = self.to_bytes_for_signing();
        self.hash = Some(Hash256::hash_from_slice(&bytes, key))
    }

    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    pub fn out(&self) -> Option<&Output> {
        self.out.as_ref()
    }

    pub fn is_coinbase(&self) -> bool {
        self.out.is_none()
    }

    pub fn is_coloured(&self) -> bool {
        self.colour_script.is_some()
    }

    pub fn verify<'a, 's, B: ShardBackend<'s>>(
        &'a self,
        height: u64,
        sum: &mut Money,
        transcripts: &mut Vec<&'a [u8]>,
        signatures: &mut Vec<SchnorSig>,
        public_keys: &mut Vec<SchnorPK>,
        shard: &Shard<'s, B>,
    ) -> Result<(), TxVerifyErr> {
        if self.is_coinbase() {
            // if height < out_height + COINBASE_EPOCH_LEN {
            //     return Err(TxVerifyErr::CoinbaseOutSpentBeforeMaturation);
            // }

            unimplemented!()
        }

        //self.out.verify(sum)?;
        let key = shard.shard_config().key();

        // Get script hash according to spend proof, address and script hash
        let oracle_script_hash = if let Some(ref spend_proof) = self.spend_proof {
            let mut out = self.script.to_script_hash(key);
            out.0 = Hash160::hash_from_slice(
                &[
                    &self.spending_pkey.as_ref().unwrap().0.to_bytes(),
                    out.0.as_slice(),
                ]
                .concat(),
                key,
            )
            .0;

            for l in spend_proof.iter() {
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
        //public_keys.push(out.pub_key());
        Ok(())
    }

    pub fn get_flags(&self) -> Result<InputFlags, &'static str> {
        let flags = match (
            self.is_coinbase(),
            self.is_coloured(),
            self.spending_pkey.is_some(),
            self.witness.is_some(),
            self.colour_script_args.is_some(),
            self.spend_proof.is_some(),
            self.colour_proof.is_some(),
            self.colour_proof_without_address.is_some(),
        ) {
            (true, false, false, false, false, false, false, false) => InputFlags::IsCoinbase,
            (true, true, false, false, true, false, true, false) => {
                InputFlags::IsColouredCoinbaseWithColourProof
            }
            (true, true, false, false, true, false, false, true) => {
                InputFlags::IsColouredCoinbaseWithColourProofWithoutAddress
            }
            (false, false, true, true, false, false, false, false) => InputFlags::Plain,
            (false, false, true, true, false, true, false, false) => InputFlags::HasSpendProof,
            (false, true, true, true, false, false, false, false) => InputFlags::IsColoured,
            (false, true, true, true, false, false, true, false) => {
                InputFlags::IsColouredHasColourProof
            }
            (false, true, true, true, false, false, false, true) => {
                InputFlags::IsColouredHasColourProofWithoutAddress
            }
            (false, true, true, true, false, true, false, false) => {
                InputFlags::IsColouredHasSpendProof
            }
            (false, true, true, true, false, true, true, false) => {
                InputFlags::IsColouredHasSpendProofAndColourProof
            }
            (false, true, true, true, false, true, false, true) => {
                InputFlags::IsColouredHasSpendProofAndColourProofWithoutAddress
            }
            (false, false, false, true, false, false, false, false) => {
                InputFlags::PlainWithoutSpendKey
            }
            (false, false, false, true, false, true, false, false) => {
                InputFlags::HasSpendProofWithoutSpendKey
            }
            (false, true, false, true, false, false, false, false) => {
                InputFlags::IsColouredWithoutSpendKey
            }
            (false, true, false, true, false, false, true, false) => {
                InputFlags::IsColouredHasColourProofWithoutSpendKey
            }
            (false, true, false, true, false, false, false, true) => {
                InputFlags::IsColouredHasColourProofWithoutAddressWithoutSpendKey
            }
            (false, true, false, true, false, true, false, false) => {
                InputFlags::IsColouredHasSpendProofWithoutSpendKey
            }
            (false, true, false, true, false, true, true, false) => {
                InputFlags::IsColouredHasSpendProofAndColourProofWithoutSpendKey
            }
            (false, true, false, true, false, true, false, true) => {
                InputFlags::IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey
            }
            _ => return Err("invalid input struct"),
        };

        Ok(flags)
    }
}

impl Encode for Input {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        let flags = self
            .get_flags()
            .map_err(|err| bincode::error::EncodeError::OtherString(err.to_owned()))?;
        let flags_to_write: u8 = flags as u8;
        bincode::Encode::encode(&flags_to_write, encoder)?;

        match flags {
            InputFlags::IsCoinbase => {
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.nsequence.to_le_bytes(), encoder)?;
            }

            InputFlags::IsColouredCoinbase => {
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.nsequence.to_le_bytes(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseWithColourProof => {
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.colour_proof.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.nsequence.to_le_bytes(), encoder)?;
            }

            InputFlags::IsColouredCoinbaseWithColourProofWithoutAddress => {
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(self.colour_script.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.colour_script_args.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(
                    self.colour_proof_without_address.as_ref().unwrap(),
                    encoder,
                )?;
                bincode::Encode::encode(&self.nsequence.to_le_bytes(), encoder)?;
            }

            InputFlags::Plain => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.witness.as_ref().unwrap().to_bytes(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.nsequence.to_le_bytes(), encoder)?;
            }

            InputFlags::HasSpendProof => {
                bincode::Encode::encode(self.out.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.spending_pkey.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.witness.as_ref().unwrap().to_bytes(), encoder)?;
                bincode::Encode::encode(&self.script, encoder)?;
                bincode::Encode::encode(&self.script_args, encoder)?;
                bincode::Encode::encode(&self.spend_proof.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(&self.nsequence.to_le_bytes(), encoder)?;
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

            InputFlags::IsColouredCoinbaseWithColourProofWithoutAddress => {
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
        let flags: u8 = bincode::Decode::decode(decoder)?;
        let flags: InputFlags = flags.try_into().map_err(|err: &'static str| {
            bincode::error::DecodeError::OtherString(err.to_owned())
        })?;

        match flags {
            InputFlags::IsCoinbase => {
                let script = bincode::Decode::decode(decoder)?;
                let script_args = bincode::Decode::decode(decoder)?;
                let nsequence: [u8; 4] = bincode::Decode::decode(decoder)?;
                let nsequence = u32::from_le_bytes(nsequence);

                Ok(Self {
                    script,
                    script_args,
                    nsequence,
                    colour_script: None,
                    colour_script_args: None,
                    spending_pkey: None,
                    spend_proof: None,
                    witness: None,
                    colour_proof: None,
                    colour_proof_without_address: None,
                    out: None,
                    hash: None,
                })
            }

            InputFlags::IsColouredCoinbase => {
                unimplemented!()
            }

            InputFlags::IsColouredCoinbaseWithColourProof => {
                unimplemented!()
            }

            InputFlags::IsColouredCoinbaseWithColourProofWithoutAddress => {
                unimplemented!()
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
                let script_args = bincode::Decode::decode(decoder)?;
                let nsequence: [u8; 4] = bincode::Decode::decode(decoder)?;
                let nsequence = u32::from_le_bytes(nsequence);

                Ok(Self {
                    script,
                    script_args,
                    nsequence,
                    colour_script: None,
                    colour_script_args: None,
                    spending_pkey,
                    spend_proof: None,
                    witness,
                    colour_proof: None,
                    colour_proof_without_address: None,
                    out,
                    hash: None,
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

            InputFlags::IsColouredCoinbaseWithColourProofWithoutAddress => {
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

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum InputFlags {
    IsCoinbase = 0x00,
    IsColouredCoinbase = 0x01,
    IsColouredCoinbaseWithColourProof = 0x02,
    IsColouredCoinbaseWithColourProofWithoutAddress = 0x03,
    Plain = 0x04,
    HasSpendProof = 0x05,
    IsColoured = 0x06,
    IsColouredHasColourProof = 0x07,
    IsColouredHasColourProofWithoutAddress = 0x08,
    IsColouredHasSpendProof = 0x09,
    IsColouredHasSpendProofAndColourProof = 0x0a,
    IsColouredHasSpendProofAndColourProofWithoutAddress = 0x0b,
    PlainWithoutSpendKey = 0x0c,
    HasSpendProofWithoutSpendKey = 0x0d,
    IsColouredWithoutSpendKey = 0x0e,
    IsColouredHasColourProofWithoutSpendKey = 0x0f,
    IsColouredHasColourProofWithoutAddressWithoutSpendKey = 0x10,
    IsColouredHasSpendProofWithoutSpendKey = 0x11,
    IsColouredHasSpendProofAndColourProofWithoutSpendKey = 0x12,
    IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey = 0x13,
}

impl std::convert::TryFrom<u8> for InputFlags {
    type Error = &'static str;

    fn try_from(num: u8) -> Result<Self, Self::Error> {
        match num {
            0x00 => Ok(Self::IsCoinbase),
            0x01 => Ok(Self::IsColouredCoinbase),
            0x02 => Ok(Self::IsColouredCoinbaseWithColourProof),
            0x03 => Ok(Self::IsColouredCoinbaseWithColourProofWithoutAddress),
            0x04 => Ok(Self::Plain),
            0x05 => Ok(Self::HasSpendProof),
            0x06 => Ok(Self::IsColoured),
            0x07 => Ok(Self::IsColouredHasColourProof),
            0x08 => Ok(Self::IsColouredHasColourProofWithoutAddress),
            0x09 => Ok(Self::IsColouredHasSpendProof),
            0x0a => Ok(Self::IsColouredHasSpendProofAndColourProof),
            0x0b => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutAddress),
            0x0c => Ok(Self::PlainWithoutSpendKey),
            0x0d => Ok(Self::HasSpendProofWithoutSpendKey),
            0x0e => Ok(Self::IsColouredWithoutSpendKey),
            0x0f => Ok(Self::IsColouredHasColourProofWithoutSpendKey),
            0x10 => Ok(Self::IsColouredHasColourProofWithoutAddressWithoutSpendKey),
            0x11 => Ok(Self::IsColouredHasSpendProofWithoutSpendKey),
            0x12 => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutSpendKey),
            0x13 => Ok(Self::IsColouredHasSpendProofAndColourProofWithoutAddressWithoutSpendKey),
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
            out: None,
            witness: None,
            spend_proof: None,
            colour_proof: None,
            colour_proof_without_address: None,
            spending_pkey: None,
            colour_script: None,
            colour_script_args: None,
            script: Script::new_coinbase(),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned64(1654654645645),
                VmTerm::Unsigned32(543543),
            ],
            nsequence: 0xffffffff,
            hash: None,
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
            spend_proof: None,
            colour_proof: None,
            colour_proof_without_address: None,
            spending_pkey: Some(PublicKey::zero()),
            colour_script: None,
            colour_script_args: None,
            script: Script::new_simple_spend(),
            script_args: vec![
                VmTerm::Signed128(137),
                VmTerm::Hash160(Address::zero().0),
                VmTerm::Hash160(Hash160::zero().0),
                VmTerm::Unsigned64(155645654645),
                VmTerm::Unsigned32(543543),
            ],
            nsequence: 0xffffffff,
            hash: None,
        };

        let decoded: Input =
            crate::codec::decode(&crate::codec::encode_to_vec(&input).unwrap()).unwrap();
        assert_eq!(decoded, input);
    }
}
