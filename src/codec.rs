// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use bincode::enc::write::Writer;

pub const CODEC_BYTES_LIMIT: usize = 1_000_000;

pub fn encode_to_vec<T: bincode::Encode>(val: &T) -> Result<Vec<u8>, bincode::error::EncodeError> {
    let config = bincode::config::standard()
        .with_little_endian()
        .with_variable_int_encoding()
        .skip_fixed_array_length()
        .with_limit::<CODEC_BYTES_LIMIT>();

    bincode::encode_to_vec(val, config)
}

pub fn encode<W: Writer, T: bincode::Encode>(
    writer: W,
    val: &T,
) -> Result<(), bincode::error::EncodeError> {
    let config = bincode::config::standard()
        .with_little_endian()
        .with_variable_int_encoding()
        .skip_fixed_array_length()
        .with_limit::<CODEC_BYTES_LIMIT>();

    bincode::encode_into_writer(val, writer, config)
}

pub fn decode<T: bincode::Decode>(bytes: &[u8]) -> Result<T, bincode::error::DecodeError> {
    let config = bincode::config::standard()
        .with_little_endian()
        .with_variable_int_encoding()
        .skip_fixed_array_length()
        .with_limit::<CODEC_BYTES_LIMIT>();

    bincode::decode_from_slice(bytes, config).map(|r| r.0)
}

#[inline]
pub fn decode_fixed_u16<D: bincode::de::Decoder>(
    decoder: &mut D,
) -> Result<u16, bincode::error::DecodeError> {
    let v: [u8; 2] = bincode::Decode::decode(decoder)?;
    Ok(u16::from_le_bytes(v))
}

#[inline]
pub fn decode_fixed_u32<D: bincode::de::Decoder>(
    decoder: &mut D,
) -> Result<u32, bincode::error::DecodeError> {
    let v: [u8; 4] = bincode::Decode::decode(decoder)?;
    Ok(u32::from_le_bytes(v))
}

#[inline]
pub fn encode_fixed_14_array_u32<E: bincode::enc::Encoder>(
    s: &[u32; 14],
    encoder: &mut E,
) -> core::result::Result<(), bincode::error::EncodeError> {
    let mut v: [u8; 56] = [0; 56];

    for i in 0..14 {
        let vs = s[i].to_le_bytes();
        let j = i * 4;
        v[j] = vs[0];
        v[j + 1] = vs[1];
        v[j + 2] = vs[2];
        v[j + 3] = vs[3];
    }

    bincode::Encode::encode(&v, encoder)
}

#[inline]
pub fn decode_fixed_14_array_u32<D: bincode::de::Decoder>(
    decoder: &mut D,
) -> Result<[u32; 14], bincode::error::DecodeError> {
    let v: [u8; 56] = bincode::Decode::decode(decoder)?;
    let mut out: [u32; 14] = [0; 14];

    for i in 0..14 {
        let j = i * 4;
        let n = &v[j..j + 4];
        let mut nn = [0; 4];
        nn.copy_from_slice(n);
        out[i] = u32::from_le_bytes(nn);
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bincode::{Decode, Encode};

    #[derive(Encode, Decode)]
    enum TestEnum {
        A(u32),
        B(u32),
    }

    struct TestWrapper(pub [u32; 14]);

    impl Encode for TestWrapper {
        fn encode<E: bincode::enc::Encoder>(
            &self,
            encoder: &mut E,
        ) -> core::result::Result<(), bincode::error::EncodeError> {
            encode_fixed_14_array_u32(&self.0, encoder)?;
            Ok(())
        }
    }

    impl Decode for TestWrapper {
        fn decode<D: bincode::de::Decoder>(
            decoder: &mut D,
        ) -> core::result::Result<Self, bincode::error::DecodeError> {
            Ok(Self(decode_fixed_14_array_u32(decoder)?))
        }
    }

    #[test]
    fn test_single_byte_enum_variant() {
        let encoded = encode_to_vec(&TestEnum::B(0)).unwrap();
        assert_eq!(encoded.as_slice(), &[1, 0]);
    }

    #[test]
    fn test_single_byte_u8() {
        let byte: u8 = 0xff;
        let encoded = encode_to_vec(&byte).unwrap();
        assert_eq!(encoded.as_slice(), &[0xff]);
    }

    #[test]
    fn test_single_byte_vec_u8() {
        let input: Vec<u8> = vec![0xff, 0xff];
        let encoded = encode_to_vec(&input).unwrap();
        assert_eq!(encoded.as_slice(), &[0x02, 0xff, 0xff]);
    }

    #[test]
    fn encode_decode_fixed_u32_24() {
        let to_encode: [u32; 14] = [0x0100_0000; 14];
        let wrapper = TestWrapper(to_encode);
        let encoded = encode_to_vec(&wrapper).unwrap();
        assert_eq!(
            encoded.as_slice(),
            &[
                0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
                0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
                0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
                0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
            ]
        );
        let decoded: TestWrapper = decode(encoded.as_slice()).unwrap();
        assert_eq!(decoded.0, to_encode);
    }
}
