// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use bincode::{Decode, Encode};
use num_derive::{FromPrimitive, ToPrimitive};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Encode, Decode, FromPrimitive, ToPrimitive)]
#[repr(u8)]
pub enum OP {
    Func = 0x00,
    BaseContext = 0x01,
    OpenImplicitCert = 0x02,
    OpenImplicitCertGlobal = 0x03,
    OpenImplicitCertScoped = 0x04,
    VerifyInline = 0x05,
    Ok = 0x06,
    ChainId = 0x07,
    ChainHeight = 0x08,
    ChainTimestamp = 0x09,
    Pi = 0x0a,
    PrevBlockHash = 0x0b,
    NetworkName = 0x0c,
    RandomHash160Var = 0x0d,
    RandomHash256Var = 0x0e,
    RandomHash512Var = 0x0f,
    RandomUnsigned8Var = 0x10,
    RandomUnsigned16Var = 0x11,
    RandomUnsigned32Var = 0x12,
    RandomUnsigned64Var = 0x13,
    RandomUnsigned128Var = 0x14,
    RandomSigned8Var = 0x15,
    RandomSigned16Var = 0x16,
    RandomSigned32Var = 0x17,
    RandomSigned64Var = 0x18,
    RandomSigned128Var = 0x19,
    RandomFloat32Var = 0x1a,
    RandomFloat64Var = 0x1b,
    RandomDecimalVar = 0x1c,
    Floor = 0x1d,
    Ceil = 0x1e,
    IsNaN = 0x1f,
    IsInfinite = 0x20,
    Ln = 0x21,
    Exp = 0x22,
    Hash160Var = 0x23,
    Hash256Var = 0x24,
    Hash512Var = 0x25,
    Unsigned8Var = 0x26,
    Unsigned16Var = 0x27,
    Unsigned32Var = 0x28,
    Unsigned64Var = 0x29,
    Unsigned128Var = 0x2a,
    UnsignedBigVar = 0x2b,
    Signed8Var = 0x2c,
    Signed16Var = 0x2d,
    Signed32Var = 0x2e,
    Signed64Var = 0x2f,
    Signed128Var = 0x30,
    SignedBigVar = 0x31,
    Float32Var = 0x32,
    Float64Var = 0x33,
    DecimalVar = 0x34,
    Hash160ArrayVar = 0x35,
    Hash256ArrayVar = 0x36,
    Hash512ArrayVar = 0x37,
    Unsigned8ArrayVar = 0x38,
    Unsigned16ArrayVar = 0x39,
    Unsigned32ArrayVar = 0x3a,
    Unsigned64ArrayVar = 0x3b,
    Unsigned128ArrayVar = 0x3c,
    UnsignedBigArrayVar = 0x3d,
    Signed8ArrayVar = 0x3e,
    Signed16ArrayVar = 0x3f,
    Signed32ArrayVar = 0x40,
    Signed64ArrayVar = 0x41,
    Signed128ArrayVar = 0x42,
    SignedBigArrayVar = 0x43,
    Float32ArrayVar = 0x44,
    Float64ArrayVar = 0x45,
    DecimalArrayVar = 0x46,
    GetAtArray = 0x47,
    PushBackArray = 0x48,
    PushFrontArray = 0x49,
    ArrayLen = 0x4a,
    GetType = 0x4b,
    PopBackArray = 0x4c,
    PopFrontArray = 0x4d,
    DeleteAtArray = 0x4e,
    ClearStack = 0x4f,
    Add = 0x50,
    Sub = 0x51,
    Mult = 0x52,
    Div = 0x53,
    BitSHLeft = 0x54,
    BitSHRight = 0x55,
    BitXOR = 0x56,
    Loop = 0x57,
    Break = 0x58,
    BreakIf = 0x59,
    BreakIfn = 0x5a,
    BreakIfEq = 0x5b,
    BreakIfNeq = 0x5c,
    BreakIfLeq = 0x5d,
    BreakIfGeq = 0x5e,
    BreakIfLt = 0x5f,
    BreakIfGt = 0x60,
    Continue = 0x61,
    ContinueIf = 0x62,
    ContinueIfn = 0x63,
    ContinueIfEq = 0x64,
    ContinueIfNeq = 0x65,
    ContinueIfLeq = 0x66,
    ContinueIfGeq = 0x67,
    ContinueIfLt = 0x68,
    ContinueIfGt = 0x69,
    Depth = 0x6a,
    Factorial = 0x6b,
    Drop = 0x6c,
    Dup = 0x6d,
    Nip = 0x6e,
    Over = 0x6f,
    Pick = 0x70,
    Roll = 0x71,
    Rot = 0x72,
    Swap = 0x73,
    Tuck = 0x74,
    Drop2 = 0x75,
    Dup2 = 0x76,
    Dup3 = 0x77,
    Over2 = 0x78,
    Rot2 = 0x79,
    Swap2 = 0x7a,
    Size = 0x7b,
    Substr = 0x7c,
    BitAND = 0x7d,
    BitOR = 0x7e,
    BitInvert = 0x7f,
    DupAll = 0x80,
    IsUTF8 = 0x81,
    Add1 = 0x82,
    Sub1 = 0x83,
    Min = 0x84,
    Max = 0x85,
    Within = 0x86,
    BoolAnd = 0x87,
    BoolOr = 0x88,
    Negate = 0x89,
    Abs = 0x8a,
    Pow = 0x8b,
    Rem = 0x8c,
    Round = 0x8d,
    PushExecCount = 0x8e,
    FlushToScriptOuts = 0x8f,
    PopToScriptOuts = 0x90,
    PickToScriptOuts = 0x91,
    TrapIf = 0x92,
    TrapIfEq = 0x93,
    TrapIfNeq = 0x94,
    TrapIfLeq = 0x95,
    TrapIfGeq = 0x96,
    TrapIfLt = 0x97,
    TrapIfGt = 0x98,
    TrapIfNeqType = 0x99,
    ToHex = 0x9a,
    FromHex = 0x9b,
    InputsLen = 0x9c,
    OutputsLen = 0x9d,
    PeekArray = 0x9e,
    ClearArray = 0x9f,
    VerifyEd25519 = 0xa0,
    VerifyEd25519Inline = 0xa1,
    VerifyEcdsa = 0xa2,
    VerifyEcdsaInline = 0xa3,
    VerifyBIP340 = 0xa4,
    VerifyBIP340Inline = 0xa5,
    GetOutAmount = 0xa6,
    GetOutReceiver = 0xa7,
    GetOutScriptHash = 0xa8,
    GetOutScriptOutsLen = 0xa9,
    GetOutScriptOut = 0xaa,
    SpillScriptOuts = 0xab,
    IsColouredOut = 0xac,
    ColourHash = 0xad,
    CallBody = 0xae,
    Call = 0xaf,
    Concat = 0xb0,
    Eq = 0xb1,
    Neq = 0xb2,
    If = 0xb3,
    Ifn = 0xb4,
    Else = 0xb5,
    End = 0xb6,
    Verify = 0xb7,
    ReturnFunc = 0xb8,
    Return = 0xb9,
    EqVerify = 0xba,
    Lt = 0xbb,
    Gt = 0xbc,
    Leq = 0xbd,
    Geq = 0xbe,
    IfLt = 0xbf,
    IfGt = 0xc0,
    IfLeq = 0xc1,
    IfGeq = 0xc2,
    IfEq = 0xc3,
    IfNeq = 0xc4,
    LtVerify = 0xc5,
    GtVerify = 0xc6,
    LeqVerify = 0xc7,
    GeqVerify = 0xc8,
    NeqVerify = 0xc9,
    CastTo = 0xca,
    InputScriptArgsLen = 0xcb,
    GetInputScriptArgAt = 0xcc,
    SpillInputScriptArgs = 0xcd,
    Sqrt = 0xce,
    Zero = 0xcf,
    One = 0xd0,
    ZeroOfType = 0xd1,
    OneOfType = 0xd2,
    PushOut = 0xd3,
    PushOutVerify = 0xd4,
    PushOutIf = 0xd5,
    PushOutIfEq = 0xd6,
    PushOutIfNeq = 0xd7,
    PushOutIfLt = 0xd8,
    PushOutIfGt = 0xd9,
    PushOutIfLeq = 0xda,
    PushOutIfGeq = 0xdb,
    GetSpentOutAmount = 0xdc,
    GetSpentOutReceiver = 0xde,
    GetSpentOutScriptHash = 0xdf,
    GetSpentOutScriptOutsLen = 0xe0,
    GetSpentOutScriptOut = 0xe1,
    SpillSpentOutScriptOuts = 0xe2,
    SpentOutIsColouredOut = 0xe3,
    CurrentColourHash = 0xe4,
    PushPrevScriptOuts = 0xe5,
    Trunc = 0xe6,
    Frac = 0xe7,
    GhostRider = 0xe8,
    Fugue = 0xe9,
    JH256 = 0xea,
    Blake2s256 = 0xeb,
    Trap = 0xec,
    Sha256 = 0xed,
    Sha512 = 0xee,
    Keccak256 = 0xef,
    Keccak512 = 0xf0,
    Blake2b256 = 0xf1,
    Blake2b512 = 0xf2,
    Blake3_160 = 0xf3,
    Blake3_256 = 0xf4,
    Blake3_512 = 0xf5,
    Blake3_256_160 = 0xf6,
    Blake3_256Keyed = 0xf7,
    Blake3_512Keyed = 0xf8,
    Blake3_160Keyed = 0xf9,
    Blake3_160Internal = 0xfa,
    Blake3_256Internal = 0xfb,
    Blake3_512Internal = 0xfc,
    Blake3_256_160Internal = 0xfd,
    Ripemd160 = 0xfe,
    Nop = 0xff,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_encodes_opcode_to_byte() {
        let encoded = crate::codec::encode_to_vec(&OP::Func).unwrap();
        assert_eq!(encoded.as_slice(), &[0x00]);
        let encoded = crate::codec::encode_to_vec(&OP::PushOut).unwrap();
        assert_eq!(encoded.as_slice(), &[0xd3]);
        let encoded = crate::codec::encode_to_vec(&OP::Nop).unwrap();
        assert_eq!(encoded.as_slice(), &[0xff]);
    }
}
