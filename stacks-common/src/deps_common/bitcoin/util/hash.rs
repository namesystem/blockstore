// Rust Bitcoin Library
// Written in 2014 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! Hash functions
//!
//! Utility functions related to hashing data, including merkleization

use std::char::from_digit;
use std::cmp::min;
use std::io::{Cursor, Write};
use std::{error, fmt, mem};

use ripemd::Ripemd160;
#[cfg(feature = "serde")]
use serde;
use sha2::{Digest, Sha256};

use crate::deps_common::bitcoin::network::encodable::{ConsensusDecodable, ConsensusEncodable};
use crate::deps_common::bitcoin::network::serialize::{
    self, BitcoinHash, RawEncoder, SimpleEncoder,
};
use crate::util::hash::bytes_to_hex;
use crate::util::uint::Uint256;
use crate::util::HexError;

/// A Bitcoin hash, 32-bytes, computed from x as SHA256(SHA256(x))
// This doesn't make much sense to me, but is implicit behaviour
// in the C++ reference client, so we need it for consensus.
#[derive(Default)]
pub struct Sha256dHash(pub [u8; 32]);
impl_array_newtype!(Sha256dHash, u8, 32);

/// An object that allows serializing data into a sha256d
pub struct Sha256dEncoder(Sha256);

/// A RIPEMD-160 hash
pub struct Ripemd160Hash([u8; 20]);
impl_array_newtype!(Ripemd160Hash, u8, 20);

/// A Bitcoin hash160, 20-bytes, computed from x as RIPEMD160(SHA256(x))
pub struct Hash160([u8; 20]);
impl_array_newtype!(Hash160, u8, 20);

impl Hash160 {
    /// Convert the Hash160 inner bytes to a non-prefixed hex string
    pub fn to_hex(&self) -> String {
        bytes_to_hex(&self.0)
    }

    /// Try to instantiate a Hash160 using the exact inner bytes of the hash.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut return_bytes = [0; 20];
        if bytes.len() != return_bytes.len() {
            return None;
        }
        return_bytes.copy_from_slice(bytes);
        Some(Self(return_bytes))
    }
}

impl Default for Sha256dEncoder {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256dEncoder {
    /// Create a new encoder
    pub fn new() -> Sha256dEncoder {
        Sha256dEncoder(Sha256::new())
    }

    /// Extract the hash from an encoder
    pub fn into_hash(self) -> Sha256dHash {
        let mut second_sha = Sha256::new();
        let mut tmp = [0; 32];
        tmp.copy_from_slice(self.0.finalize().as_slice());
        second_sha.update(tmp);
        tmp.copy_from_slice(second_sha.finalize().as_slice());
        Sha256dHash(tmp)
    }
}

impl SimpleEncoder for Sha256dEncoder {
    fn emit_u64(&mut self, v: u64) -> Result<(), serialize::Error> {
        let mut data = [0; 8];
        (&mut data[..]).write_all(&v.to_le_bytes()).unwrap();
        self.0.update(data);
        Ok(())
    }

    fn emit_u32(&mut self, v: u32) -> Result<(), serialize::Error> {
        let mut data = [0; 4];
        (&mut data[..]).write_all(&v.to_le_bytes()).unwrap();
        self.0.update(data);
        Ok(())
    }

    fn emit_u16(&mut self, v: u16) -> Result<(), serialize::Error> {
        let mut data = [0; 2];
        (&mut data[..]).write_all(&v.to_le_bytes()).unwrap();
        self.0.update(data);
        Ok(())
    }

    fn emit_i64(&mut self, v: i64) -> Result<(), serialize::Error> {
        let mut data = [0; 8];
        (&mut data[..]).write_all(&v.to_le_bytes()).unwrap();
        self.0.update(data);
        Ok(())
    }

    fn emit_i32(&mut self, v: i32) -> Result<(), serialize::Error> {
        let mut data = [0; 4];
        (&mut data[..]).write_all(&v.to_le_bytes()).unwrap();
        self.0.update(data);
        Ok(())
    }

    fn emit_i16(&mut self, v: i16) -> Result<(), serialize::Error> {
        let mut data = [0; 2];
        (&mut data[..]).write_all(&v.to_le_bytes()).unwrap();
        self.0.update(data);
        Ok(())
    }

    fn emit_i8(&mut self, v: i8) -> Result<(), serialize::Error> {
        self.0.update([v as u8]);
        Ok(())
    }

    fn emit_u8(&mut self, v: u8) -> Result<(), serialize::Error> {
        self.0.update([v]);
        Ok(())
    }

    fn emit_bool(&mut self, v: bool) -> Result<(), serialize::Error> {
        self.0.update([if v { 1 } else { 0 }]);
        Ok(())
    }
}

impl Ripemd160Hash {
    /// Create a hash by hashing some data
    pub fn from_data(data: &[u8]) -> Ripemd160Hash {
        let mut ret = [0; 20];
        let mut rmd = Ripemd160::new();
        rmd.update(data);
        ret.copy_from_slice(rmd.finalize().as_slice());
        Ripemd160Hash(ret)
    }
}

impl Hash160 {
    /// Create a hash by hashing some data
    pub fn from_data(data: &[u8]) -> Hash160 {
        let mut tmp = [0; 32];
        let mut ret = [0; 20];
        let mut sha2 = Sha256::new();
        let mut rmd = Ripemd160::new();
        sha2.update(data);
        tmp.copy_from_slice(sha2.finalize().as_slice());
        rmd.update(tmp);
        ret.copy_from_slice(rmd.finalize().as_slice());
        Hash160(ret)
    }
}

impl Sha256dHash {
    /// Create a hash by hashing some data
    pub fn from_data(data: &[u8]) -> Sha256dHash {
        use sha2::Digest;

        let Sha256dHash(mut ret): Sha256dHash = Default::default();
        let mut sha2 = Sha256::new();
        let mut sha2_2 = Sha256::new();
        sha2.update(data);
        ret.copy_from_slice(sha2.finalize().as_slice());
        sha2_2.update(ret);
        ret.copy_from_slice(sha2_2.finalize().as_slice());
        Sha256dHash(ret)
    }

    /// Converts a hash to a little-endian Uint256
    #[inline]
    pub fn into_le(self) -> Uint256 {
        let Sha256dHash(data) = self;
        let mut ret: [u64; 4] = unsafe { mem::transmute(data) };
        for x in ret.iter_mut() {
            *x = x.to_le();
        }
        Uint256(ret)
    }

    /// Converts a hash to a big-endian Uint256
    #[inline]
    pub fn into_be(self) -> Uint256 {
        let Sha256dHash(mut data) = self;
        data.reverse();
        let mut ret: [u64; 4] = unsafe { mem::transmute(data) };
        for x in ret.iter_mut() {
            *x = x.to_be();
        }
        Uint256(ret)
    }

    // Human-readable hex output

    /// Decodes a big-endian (i.e. reversed vs sha256sum output) hex string as a Sha256dHash
    #[inline]
    pub fn from_hex(s: &str) -> Result<Sha256dHash, HexError> {
        if s.len() != 64 {
            return Err(HexError::BadLength(s.len()));
        }

        let bytes = s.as_bytes();
        let mut ret = [0; 32];
        for i in 0..32 {
            let hi = match bytes[2 * i] {
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'f' => b - b'a' + 10,
                b @ b'A'..=b'F' => b - b'A' + 10,
                b => return Err(HexError::BadCharacter(b as char)),
            };
            let lo = match bytes[2 * i + 1] {
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'f' => b - b'a' + 10,
                b @ b'A'..=b'F' => b - b'A' + 10,
                b => return Err(HexError::BadCharacter(b as char)),
            };
            ret[31 - i] = hi * 0x10 + lo;
        }
        Ok(Sha256dHash(ret))
    }

    /// Decodes a little-endian (i.e. same as sha256sum output) hex string as a Sha256dHash
    #[inline]
    pub fn from_hex_le(s: &str) -> Result<Sha256dHash, HexError> {
        if s.len() != 64 {
            return Err(HexError::BadLength(s.len()));
        }

        let bytes = s.as_bytes();
        let mut ret = [0; 32];
        for i in 0..32 {
            let hi = match bytes[2 * i] {
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'f' => b - b'a' + 10,
                b @ b'A'..=b'F' => b - b'A' + 10,
                b => return Err(HexError::BadCharacter(b as char)),
            };
            let lo = match bytes[2 * i + 1] {
                b @ b'0'..=b'9' => b - b'0',
                b @ b'a'..=b'f' => b - b'a' + 10,
                b @ b'A'..=b'F' => b - b'A' + 10,
                b => return Err(HexError::BadCharacter(b as char)),
            };
            ret[i] = hi * 0x10 + lo;
        }
        Ok(Sha256dHash(ret))
    }

    /// Human-readable hex output
    pub fn le_hex_string(&self) -> String {
        let &Sha256dHash(data) = self;
        let mut ret = String::with_capacity(64);
        for item in data.iter().take(32) {
            ret.push(from_digit((*item / 0x10) as u32, 16).unwrap());
            ret.push(from_digit((*item & 0x0f) as u32, 16).unwrap());
        }
        ret
    }

    /// Human-readable hex output
    pub fn be_hex_string(&self) -> String {
        let &Sha256dHash(data) = self;
        let mut ret = String::with_capacity(64);
        for i in (0..32).rev() {
            ret.push(from_digit((data[i] / 0x10) as u32, 16).unwrap());
            ret.push(from_digit((data[i] & 0x0f) as u32, 16).unwrap());
        }
        ret
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Sha256dHash {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use std::fmt::{self, Formatter};

        struct Visitor;
        impl<'de> serde::de::Visitor<'de> for Visitor {
            type Value = Sha256dHash;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                formatter.write_str("a SHA256d hash")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Sha256dHash::from_hex(v).map_err(E::custom)
            }

            fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(v)
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(&v)
            }
        }

        deserializer.deserialize_str(Visitor)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Sha256dHash {
    /// Serialize a `Sha256dHash`.
    ///
    /// Note that this outputs hashes as big endian hex numbers, so this should be
    /// used only for user-facing stuff. Internal and network serialization is
    /// little-endian and should be done using the consensus
    /// [`ConsensusEncodable`][1] interface.
    ///
    /// [1]: ../../network/encodable/trait.ConsensusEncodable.html
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use std::{char, str};

        let mut string = [0; 64];
        for i in 0..32 {
            string[2 * i] = char::from_digit((self.0[31 - i] / 0x10) as u32, 16).unwrap() as u8;
            string[2 * i + 1] = char::from_digit((self.0[31 - i] & 0x0f) as u32, 16).unwrap() as u8;
        }

        let hex_str = unsafe { str::from_utf8_unchecked(&string) };
        serializer.serialize_str(hex_str)
    }
}

// Debug encodings (no reversing)
impl fmt::Debug for Sha256dHash {
    /// Output the raw sha256d hash, not reversing it (unlike Display and what Core does for user display)
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Sha256dHash(data) = self;
        for ch in data.iter() {
            write!(f, "{:02x}", ch)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Hash160 {
    /// Output the raw hash160 hash, not reversing it (nothing reverses the output of ripemd160 in Bitcoin)
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Hash160(data) = self;
        for ch in data.iter() {
            write!(f, "{:02x}", ch)?;
        }
        Ok(())
    }
}

// Consensus encoding (no reversing)
impl_newtype_consensus_encoding!(Sha256dHash);

// User RPC/display encoding (reversed)
impl fmt::Display for Sha256dHash {
    /// Output the sha256d hash in reverse, copying Bitcoin Core's behaviour
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(self, f)
    }
}

impl fmt::LowerHex for Sha256dHash {
    /// Output the sha256d hash in reverse, copying Bitcoin Core's behaviour
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Sha256dHash(data) = self;
        for ch in data.iter().rev() {
            write!(f, "{:02x}", ch)?;
        }
        Ok(())
    }
}

impl fmt::UpperHex for Sha256dHash {
    /// Output the sha256d hash in reverse, copying Bitcoin Core's behaviour
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let &Sha256dHash(data) = self;
        for ch in data.iter().rev() {
            write!(f, "{:02X}", ch)?;
        }
        Ok(())
    }
}

/// Any collection of objects for which a merkle root makes sense to calculate
pub trait MerkleRoot {
    /// Construct a merkle tree from a collection, with elements ordered as
    /// they were in the original collection, and return the merkle root.
    fn merkle_root(&self) -> Sha256dHash;
}

/// Calculates the merkle root of a list of txids hashes directly
pub fn bitcoin_merkle_root(data: Vec<Sha256dHash>) -> Sha256dHash {
    // Base case
    if data.is_empty() {
        return Default::default();
    }
    if data.len() == 1 {
        return data[0];
    }
    // Recursion
    let iterations = (data.len() + 1) / 2;
    let mut next = Vec::with_capacity(iterations);
    for idx in 0..iterations {
        let idx1 = 2 * idx;
        let idx2 = min(idx1 + 1, data.len() - 1);
        let mut encoder = RawEncoder::new(Cursor::new(vec![]));
        data[idx1].consensus_encode(&mut encoder).unwrap();
        data[idx2].consensus_encode(&mut encoder).unwrap();
        next.push(encoder.into_inner().into_inner().bitcoin_hash());
    }
    bitcoin_merkle_root(next)
}

impl<T: BitcoinHash> MerkleRoot for &[T] {
    fn merkle_root(&self) -> Sha256dHash {
        bitcoin_merkle_root(self.iter().map(|obj| obj.bitcoin_hash()).collect())
    }
}

impl<T: BitcoinHash> MerkleRoot for Vec<T> {
    fn merkle_root(&self) -> Sha256dHash {
        (&self[..]).merkle_root()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::deps_common::bitcoin::network::encodable::{ConsensusEncodable, VarInt};
    use crate::deps_common::bitcoin::network::serialize::{deserialize, serialize};
    use crate::util::uint::Uint256;

    #[test]
    fn test_sha256d() {
        // nb the 5df6... output is the one you get from sha256sum. this is the
        // "little-endian" hex string since it matches the in-memory representation
        // of a Uint256 (which is little-endian) after transmutation
        assert_eq!(
            Sha256dHash::from_data(&[]).le_hex_string(),
            "5df6e0e2761359d30a8275058e299fcc0381534545f55cf43e41983f5d4c9456"
        );
        assert_eq!(
            Sha256dHash::from_data(&[]).be_hex_string(),
            "56944c5d3f98413ef45cf54545538103cc9f298e0575820ad3591376e2e0f65d"
        );

        assert_eq!(
            format!("{}", Sha256dHash::from_data(&[])),
            "56944c5d3f98413ef45cf54545538103cc9f298e0575820ad3591376e2e0f65d"
        );
        assert_eq!(
            format!("{:?}", Sha256dHash::from_data(&[])),
            "5df6e0e2761359d30a8275058e299fcc0381534545f55cf43e41983f5d4c9456"
        );
        assert_eq!(
            format!("{:x}", Sha256dHash::from_data(&[])),
            "56944c5d3f98413ef45cf54545538103cc9f298e0575820ad3591376e2e0f65d"
        );
        assert_eq!(
            format!("{:X}", Sha256dHash::from_data(&[])),
            "56944C5D3F98413EF45CF54545538103CC9F298E0575820AD3591376E2E0F65D"
        );
    }

    #[test]
    fn test_sha256d_data() {
        assert_eq!(
            Sha256dHash::from_data(&[]).as_bytes(),
            &[
                0x5d, 0xf6, 0xe0, 0xe2, 0x76, 0x13, 0x59, 0xd3, 0x0a, 0x82, 0x75, 0x05, 0x8e, 0x29,
                0x9f, 0xcc, 0x03, 0x81, 0x53, 0x45, 0x45, 0xf5, 0x5c, 0xf4, 0x3e, 0x41, 0x98, 0x3f,
                0x5d, 0x4c, 0x94, 0x56,
            ]
        );
    }

    #[test]
    fn sha256d_encoder() {
        let test = vec![true, false, true, true, false];
        let mut enc = Sha256dEncoder::new();
        assert!(test.consensus_encode(&mut enc).is_ok());
        assert_eq!(
            enc.into_hash(),
            Sha256dHash::from_data(&serialize(&test).unwrap())
        );

        macro_rules! array_encode_test (
            ($ty:ty) => ({
                // try serializing the whole array
                let test: [$ty; 1000] = [1; 1000];
                let mut enc = Sha256dEncoder::new();
                assert!((&test[..]).consensus_encode(&mut enc).is_ok());
                assert_eq!(enc.into_hash(), Sha256dHash::from_data(&serialize(&test[..]).unwrap()));

                // try doing it just one object at a time
                let mut enc = Sha256dEncoder::new();
                assert!(VarInt(test.len() as u64).consensus_encode(&mut enc).is_ok());
                for obj in &test[..] {
                    assert!(obj.consensus_encode(&mut enc).is_ok());
                }
                assert_eq!(enc.into_hash(), Sha256dHash::from_data(&serialize(&test[..]).unwrap()));
            })
        );

        array_encode_test!(u64);
        array_encode_test!(u32);
        array_encode_test!(u16);
        array_encode_test!(u8);
        array_encode_test!(i64);
        array_encode_test!(i32);
        array_encode_test!(i16);
        array_encode_test!(i8);
    }

    #[test]
    fn test_consenus_encode_roundtrip() {
        let hash = Sha256dHash::from_data(&[]);
        let serial = serialize(&hash).unwrap();
        let deserial = deserialize(&serial).unwrap();
        assert_eq!(hash, deserial);
    }

    #[test]
    fn test_sighash_single_vec() {
        let one = Sha256dHash([
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ]);
        assert_eq!(one.into_le(), Uint256::from_u64(1));
    }
}
