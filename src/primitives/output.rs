// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::*;
use crate::primitives::{Address, ColouredAddress, Hash160, Hash256, TxVerifyErr};
use crate::vm::internal::VmTerm;
use bincode::{Decode, Encode};
use std::hash::{Hash, Hasher};

#[derive(PartialEq, Debug, Eq, Clone)]
pub struct Output {
    pub amount: Money,
    pub script_hash: Hash160,
    pub inputs_hash: Hash160,
    pub idx: u16,
    pub address: Option<Address>,
    pub coloured_address: Option<ColouredAddress>,
    pub coinbase_height: Option<u64>,
    pub script_outs: Vec<VmTerm>,
    pub hash: Option<Hash256>,
}

impl Hash for Output {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl Output {
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    pub fn amount(&self) -> Money {
        self.amount
    }

    pub fn verify(&self, sum: &mut Money) -> Result<(), TxVerifyErr> {
        if !money_check(self.amount) {
            return Err(TxVerifyErr::FailedMoneyCheck);
        }

        if self.amount == 0 {
            return Err(TxVerifyErr::ZeroOutputAmount);
        }

        Ok(())
    }

    pub fn is_coloured(&self) -> bool {
        self.coloured_address.is_some()
    }

    pub fn is_coinbase(&self) -> bool {
        self.coinbase_height.is_some()
    }

    pub fn coinbase_height(&self) -> Option<u64> {
        self.coinbase_height
    }

    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    pub fn compute_hash(&mut self, key: &str) {
        if self.hash.is_some() {
            return;
        }

        let bytes = self.to_bytes();
        self.hash = Some(Hash256::hash_from_slice(&bytes, key))
    }
}

impl Encode for Output {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        let flags = match (
            self.address.is_some(),
            self.coloured_address.is_some(),
            self.coinbase_height.is_some(),
        ) {
            (true, false, true) => OutputFlags::HasAdddressIsCoinbase,
            (false, true, true) => OutputFlags::HasColouredAddressIsCoinbase,
            (true, false, false) => OutputFlags::HasAddress,
            (false, true, false) => OutputFlags::HasColouredAddress,
            _ => {
                return Err(bincode::error::EncodeError::OtherString(
                    "invalid output struct".to_owned(),
                ))
            }
        };
        let flags_to_write: u8 = flags as u8;
        bincode::Encode::encode(&flags_to_write, encoder)?;
        bincode::Encode::encode(&self.amount, encoder)?;
        bincode::Encode::encode(&self.script_hash, encoder)?;
        bincode::Encode::encode(&self.inputs_hash, encoder)?;
        bincode::Encode::encode(&self.idx, encoder)?;
        bincode::Encode::encode(&self.script_outs, encoder)?;
        match flags {
            OutputFlags::HasAdddressIsCoinbase => {
                bincode::Encode::encode(self.address.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.coinbase_height.as_ref().unwrap(), encoder)?;
            }

            OutputFlags::HasColouredAddressIsCoinbase => {
                bincode::Encode::encode(self.coloured_address.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.coinbase_height.as_ref().unwrap(), encoder)?;
            }

            OutputFlags::HasAddress => {
                bincode::Encode::encode(self.address.as_ref().unwrap(), encoder)?;
            }

            OutputFlags::HasColouredAddress => {
                bincode::Encode::encode(self.coloured_address.as_ref().unwrap(), encoder)?;
            }
        };
        Ok(())
    }
}

impl Decode for Output {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let flags: u8 = bincode::Decode::decode(decoder)?;
        let flags: OutputFlags = flags.try_into().map_err(|err: &'static str| {
            bincode::error::DecodeError::OtherString(err.to_owned())
        })?;
        let amount = bincode::Decode::decode(decoder)?;
        let script_hash = bincode::Decode::decode(decoder)?;
        let inputs_hash = bincode::Decode::decode(decoder)?;
        let idx = bincode::Decode::decode(decoder)?;
        let script_outs = bincode::Decode::decode(decoder)?;
        let (address, coloured_address, coinbase_height) = match flags {
            OutputFlags::HasAdddressIsCoinbase => (
                Some(bincode::Decode::decode(decoder)?),
                None,
                Some(bincode::Decode::decode(decoder)?),
            ),

            OutputFlags::HasColouredAddressIsCoinbase => (
                None,
                Some(bincode::Decode::decode(decoder)?),
                Some(bincode::Decode::decode(decoder)?),
            ),

            OutputFlags::HasAddress => (Some(bincode::Decode::decode(decoder)?), None, None),

            OutputFlags::HasColouredAddress => {
                (None, Some(bincode::Decode::decode(decoder)?), None)
            }
        };

        Ok(Self {
            amount,
            script_hash,
            inputs_hash,
            idx,
            address,
            coloured_address,
            coinbase_height,
            script_outs,
            hash: None,
        })
    }
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Debug)]
enum OutputFlags {
    HasAdddressIsCoinbase = 0x00,
    HasColouredAddressIsCoinbase = 0x01,
    HasAddress = 0x02,
    HasColouredAddress = 0x03,
}

impl std::convert::TryFrom<u8> for OutputFlags {
    type Error = &'static str;

    fn try_from(num: u8) -> Result<Self, Self::Error> {
        match num {
            0x00 => Ok(Self::HasAdddressIsCoinbase),
            0x01 => Ok(Self::HasColouredAddressIsCoinbase),
            0x02 => Ok(Self::HasAddress),
            0x03 => Ok(Self::HasColouredAddress),
            _ => Err("invalid bitflags"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_money_checks_output_in_verify() {
        let output = Output {
            amount: -1,
            script_hash: Hash160::zero(),
            inputs_hash: Hash160::zero(),
            script_outs: vec![],
            idx: 0,
            address: None,
            coloured_address: None,
            coinbase_height: None,
            hash: None,
        };
        let mut sum = 0;

        assert_eq!(output.verify(&mut sum), Err(TxVerifyErr::FailedMoneyCheck))
    }

    #[test]
    fn it_fails_to_verify_output_with_zero_amount() {
        let output = Output {
            amount: 0,
            script_hash: Hash160::zero(),
            inputs_hash: Hash160::zero(),
            script_outs: vec![],
            idx: 0,
            address: None,
            coloured_address: None,
            coinbase_height: None,
            hash: None,
        };
        let mut sum = 0;

        assert_eq!(output.verify(&mut sum), Err(TxVerifyErr::ZeroOutputAmount))
    }

    #[test]
    fn output_encode_decode() {
        let output = Output {
            amount: 100,
            script_hash: Hash160::zero(),
            inputs_hash: Hash160::zero(),
            script_outs: vec![],
            idx: 0,
            address: Some(Address::zero()),
            coloured_address: None,
            coinbase_height: None,
            hash: None,
        };
        let decoded: Output =
            crate::codec::decode(&crate::codec::encode_to_vec(&output).unwrap()).unwrap();
        assert_eq!(decoded, output);
    }

    #[test]
    fn output_encode_decode_coinbase() {
        let output = Output {
            amount: 100,
            script_hash: Hash160::zero(),
            inputs_hash: Hash160::zero(),
            script_outs: vec![],
            idx: 0,
            address: Some(Address::zero()),
            coloured_address: None,
            coinbase_height: Some(10),
            hash: None,
        };
        let decoded: Output =
            crate::codec::decode(&crate::codec::encode_to_vec(&output).unwrap()).unwrap();
        assert_eq!(decoded, output);
    }

    #[test]
    fn output_coloured_encode_decode() {
        let output = Output {
            amount: 100,
            script_hash: Hash160::zero(),
            inputs_hash: Hash160::zero(),
            script_outs: vec![],
            idx: 0,
            coloured_address: Some(ColouredAddress::zero()),
            address: None,
            coinbase_height: None,
            hash: None,
        };
        let decoded: Output =
            crate::codec::decode(&crate::codec::encode_to_vec(&output).unwrap()).unwrap();
        assert_eq!(decoded, output);
    }

    #[test]
    fn output_coloured_encode_decode_coinbase() {
        let output = Output {
            amount: 100,
            script_hash: Hash160::zero(),
            inputs_hash: Hash160::zero(),
            script_outs: vec![],
            idx: 0,
            coloured_address: Some(ColouredAddress::zero()),
            address: None,
            coinbase_height: Some(10),
            hash: None,
        };
        let decoded: Output =
            crate::codec::decode(&crate::codec::encode_to_vec(&output).unwrap()).unwrap();
        assert_eq!(decoded, output);
    }
}
