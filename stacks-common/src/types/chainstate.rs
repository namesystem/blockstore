use std::fmt::{self, Display};
use std::io::{Read, Write};
use std::str::FromStr;

use rand::{Rng, SeedableRng};
use serde::de::{Deserialize, Error as de_Error};
use serde::ser::Error as ser_Error;
use serde::Serialize;
use sha2::{Digest as Sha2Digest, Sha256, Sha512_256};

use crate::codec::{read_next, write_next, Error as CodecError, StacksMessageCodec};
use crate::consts::{FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH};
use crate::deps_common::bitcoin::util::hash::Sha256dHash;
use crate::util::hash::{to_hex, DoubleSha256, Hash160, Sha512Trunc256Sum, HASH160_ENCODED_SIZE};
use crate::util::secp256k1::{MessageSignature, Secp256k1PrivateKey, Secp256k1PublicKey};
use crate::util::uint::Uint256;

pub type StacksPublicKey = Secp256k1PublicKey;
pub type StacksPrivateKey = Secp256k1PrivateKey;

/// Hash of a Trie node.  This is a SHA2-512/256.
#[derive(Default)]
pub struct TrieHash(pub [u8; 32]);
impl_array_newtype!(TrieHash, u8, 32);
impl_array_hexstring_fmt!(TrieHash);
impl_byte_array_newtype!(TrieHash, u8, 32);
impl_byte_array_serde!(TrieHash);

pub const TRIEHASH_ENCODED_SIZE: usize = 32;

impl TrieHash {
    pub fn from_key(k: &str) -> Self {
        Self::from_data(k.as_bytes())
    }

    /// TrieHash of zero bytes
    pub fn from_empty_data() -> TrieHash {
        // sha2-512/256 hash of empty string.
        // this is used so frequently it helps performance if we just have a constant for it.
        TrieHash([
            0xc6, 0x72, 0xb8, 0xd1, 0xef, 0x56, 0xed, 0x28, 0xab, 0x87, 0xc3, 0x62, 0x2c, 0x51,
            0x14, 0x06, 0x9b, 0xdd, 0x3a, 0xd7, 0xb8, 0xf9, 0x73, 0x74, 0x98, 0xd0, 0xc0, 0x1e,
            0xce, 0xf0, 0x96, 0x7a,
        ])
    }

    /// TrieHash from bytes
    pub fn from_data(data: &[u8]) -> TrieHash {
        if data.is_empty() {
            return TrieHash::from_empty_data();
        }

        let mut tmp = [0u8; 32];

        let mut hasher = Sha512_256::new();
        hasher.update(data);
        tmp.copy_from_slice(hasher.finalize().as_slice());

        TrieHash(tmp)
    }

    pub fn from_data_array<B: AsRef<[u8]>>(data: &[B]) -> TrieHash {
        if data.is_empty() {
            return TrieHash::from_empty_data();
        }

        let mut tmp = [0u8; 32];

        let mut hasher = Sha512_256::new();

        for item in data.iter() {
            hasher.update(item);
        }
        tmp.copy_from_slice(hasher.finalize().as_slice());
        TrieHash(tmp)
    }

    /// Convert to a String that can be used in e.g. sqlite
    /// If we did not implement this seperate from Display,
    /// we would use the stacks_common::util::hash::to_hex function
    /// which is the unrolled version of this function.
    #[allow(clippy::inherent_to_string_shadow_display)]
    pub fn to_string(&self) -> String {
        let s = format!("{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
                          self.0[0],     self.0[1],       self.0[2],       self.0[3],
                          self.0[4],     self.0[5],       self.0[6],       self.0[7],
                          self.0[8],     self.0[9],       self.0[10],      self.0[11],
                          self.0[12],    self.0[13],      self.0[14],      self.0[15],
                          self.0[16],    self.0[17],      self.0[18],      self.0[19],
                          self.0[20],    self.0[21],      self.0[22],      self.0[23],
                          self.0[24],    self.0[25],      self.0[26],      self.0[27],
                          self.0[28],    self.0[29],      self.0[30],      self.0[31]);
        s
    }
}

#[derive(Serialize, Deserialize)]
pub struct BurnchainHeaderHash(pub [u8; 32]);
impl_array_newtype!(BurnchainHeaderHash, u8, 32);
impl_array_hexstring_fmt!(BurnchainHeaderHash);
impl_byte_array_newtype!(BurnchainHeaderHash, u8, 32);

pub struct BlockHeaderHash(pub [u8; 32]);
impl_array_newtype!(BlockHeaderHash, u8, 32);
impl_array_hexstring_fmt!(BlockHeaderHash);
impl_byte_array_newtype!(BlockHeaderHash, u8, 32);
impl_byte_array_serde!(BlockHeaderHash);
pub const BLOCK_HEADER_HASH_ENCODED_SIZE: usize = 32;

#[cfg(feature = "log")]
impl slog::Value for BlockHeaderHash {
    fn serialize(
        &self,
        _record: &slog::Record,
        key: slog::Key,
        serializer: &mut dyn slog::Serializer,
    ) -> slog::Result {
        serializer.emit_arguments(key, &format_args!("{}", *self))
    }
}

/// Identifier used to identify "sortitions" in the
///  SortitionDB. A sortition is the collection of
///  valid burnchain operations (and any dependent
///  variables, e.g., the sortition winner, the
///  consensus hash, the next VRF key)
pub struct SortitionId(pub [u8; 32]);
impl_array_newtype!(SortitionId, u8, 32);
impl_array_hexstring_fmt!(SortitionId);
impl_byte_array_newtype!(SortitionId, u8, 32);

pub struct VRFSeed(pub [u8; 32]);
impl_array_newtype!(VRFSeed, u8, 32);
impl_array_hexstring_fmt!(VRFSeed);
impl_byte_array_newtype!(VRFSeed, u8, 32);
impl_byte_array_serde!(VRFSeed);

/// Identifier used to identify Proof-of-Transfer forks
///  (or Rewards Cycle forks). These identifiers are opaque
///  outside of the PoX DB, however, they are sufficient
///  to uniquely identify a "sortition" when paired with
///  a burn header hash
// TODO: Vec<bool> is an aggressively unoptimized implementation,
//       replace with a real bitvec
#[derive(Clone, Debug, PartialEq)]
pub struct PoxId(Vec<bool>);

impl SortitionId {
    pub fn stubbed(from: &BurnchainHeaderHash) -> SortitionId {
        SortitionId::new(from, &PoxId::stubbed())
    }

    pub fn new(bhh: &BurnchainHeaderHash, pox: &PoxId) -> SortitionId {
        if pox == &PoxId::stubbed() {
            SortitionId(bhh.0)
        } else {
            let mut hasher = Sha512_256::new();
            hasher.update(bhh);
            write!(hasher, "{}", pox).expect("Failed to deserialize PoX ID into the hasher");
            let h = Sha512Trunc256Sum::from_hasher(hasher);
            let s = SortitionId(h.0);
            test_debug!("SortitionId({}) = {} + {}", &s, bhh, pox);
            s
        }
    }
}

impl PoxId {
    pub fn new(contents: Vec<bool>) -> Self {
        PoxId(contents)
    }

    pub fn initial() -> PoxId {
        PoxId(vec![true])
    }

    pub fn from_bools(bools: Vec<bool>) -> PoxId {
        PoxId(bools)
    }

    pub fn extend_with_present_block(&mut self) {
        self.0.push(true);
    }
    pub fn extend_with_not_present_block(&mut self) {
        self.0.push(false);
    }

    pub fn stubbed() -> PoxId {
        PoxId(vec![])
    }

    pub fn has_ith_anchor_block(&self, i: usize) -> bool {
        if i >= self.0.len() {
            false
        } else {
            self.0[i]
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn bit_slice(&self, start: usize, len: usize) -> (Vec<u8>, u64) {
        let mut ret = vec![0x00];
        let mut count = 0;
        for bit in start..(start + len) {
            if bit >= self.len() {
                break;
            }
            let i = bit - start;
            if i > 0 && i % 8 == 0 {
                ret.push(0x00);
            }

            let sz = ret.len() - 1;
            if self.0[bit] {
                ret[sz] |= 1 << (i % 8);
            }
            count += 1;
        }
        (ret, count)
    }

    pub fn num_inventory_reward_cycles(&self) -> usize {
        self.0.len().saturating_sub(1)
    }

    pub fn has_prefix(&self, prefix: &PoxId) -> bool {
        if self.len() < prefix.len() {
            return false;
        }

        for i in 0..prefix.len() {
            if self.0[i] != prefix.0[i] {
                return false;
            }
        }

        true
    }

    pub fn into_inner(self) -> Vec<bool> {
        self.0
    }
}

impl FromStr for PoxId {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = Vec::with_capacity(s.len());
        for c in s.chars() {
            match c {
                '0' => result.push(false),
                '1' => result.push(true),
                _ => return Err("Unexpected character in PoX ID serialization"),
            }
        }
        Ok(PoxId::new(result))
    }
}

impl fmt::Display for PoxId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for val in self.0.iter() {
            write!(f, "{}", if *val { 1 } else { 0 })?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Serialize, Deserialize, Hash)]
pub struct StacksAddress {
    pub version: u8,
    pub bytes: Hash160,
}

impl StacksMessageCodec for StacksAddress {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.version)?;
        fd.write_all(self.bytes.as_bytes())
            .map_err(CodecError::WriteError)
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<StacksAddress, CodecError> {
        let version: u8 = read_next(fd)?;
        let hash160: Hash160 = read_next(fd)?;
        Ok(StacksAddress {
            version,
            bytes: hash160,
        })
    }
}

pub const STACKS_ADDRESS_ENCODED_SIZE: u32 = 1 + HASH160_ENCODED_SIZE;

/// How much work has gone into this chain so far?
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StacksWorkScore {
    pub burn: u64, // number of burn tokens destroyed
    pub work: u64, // in Stacks, "work" == the length of the fork
}

pub struct StacksBlockId(pub [u8; 32]);
impl_array_newtype!(StacksBlockId, u8, 32);
impl_array_hexstring_fmt!(StacksBlockId);
impl_byte_array_newtype!(StacksBlockId, u8, 32);
impl_byte_array_serde!(StacksBlockId);

/// A newtype for `StacksBlockId` that indicates a block is a tenure-change
/// block. This helps to explicitly differentiate tenure-change blocks in the
/// code.
pub struct TenureBlockId(pub StacksBlockId);
impl From<StacksBlockId> for TenureBlockId {
    fn from(id: StacksBlockId) -> TenureBlockId {
        TenureBlockId(id)
    }
}

pub struct ConsensusHash(pub [u8; 20]);
impl_array_newtype!(ConsensusHash, u8, 20);
impl_array_hexstring_fmt!(ConsensusHash);
impl_byte_array_newtype!(ConsensusHash, u8, 20);
impl_byte_array_serde!(ConsensusHash);

pub const CONSENSUS_HASH_ENCODED_SIZE: u32 = 20;

impl StacksBlockId {
    pub fn new(
        sortition_consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> StacksBlockId {
        let mut hasher = Sha512_256::new();
        hasher.update(block_hash);
        hasher.update(sortition_consensus_hash);

        let h = Sha512Trunc256Sum::from_hasher(hasher);
        StacksBlockId(h.0)
    }

    pub fn first_mined() -> StacksBlockId {
        StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH)
    }
}

impl StacksWorkScore {
    /// Stacks work score for the first-mined block
    pub fn initial() -> StacksWorkScore {
        StacksWorkScore {
            burn: 0,
            work: 1, // block 0 is the boot code
        }
    }

    /// Stacks work score for the boot code block
    pub fn genesis() -> StacksWorkScore {
        StacksWorkScore { burn: 0, work: 0 }
    }
}

impl StacksMessageCodec for StacksWorkScore {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.burn)?;
        write_next(fd, &self.work)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<StacksWorkScore, CodecError> {
        let burn = read_next(fd)?;
        let work = read_next(fd)?;

        Ok(StacksWorkScore { burn, work })
    }
}

impl_byte_array_message_codec!(TrieHash, TRIEHASH_ENCODED_SIZE as u32);
impl_byte_array_message_codec!(Sha512Trunc256Sum, 32);

impl_byte_array_message_codec!(ConsensusHash, 20);
impl_byte_array_message_codec!(Hash160, 20);
impl_byte_array_message_codec!(BurnchainHeaderHash, 32);
impl_byte_array_message_codec!(BlockHeaderHash, 32);
impl_byte_array_message_codec!(StacksBlockId, 32);
impl_byte_array_message_codec!(MessageSignature, 65);

impl BlockHeaderHash {
    pub fn to_hash160(&self) -> Hash160 {
        Hash160::from_sha256(&self.0)
    }

    pub fn from_serializer<C: StacksMessageCodec>(
        serializer: &C,
    ) -> Result<BlockHeaderHash, CodecError> {
        let mut hasher = Sha512_256::new();
        serializer.consensus_serialize(&mut hasher)?;
        let hash = Sha512Trunc256Sum::from_hasher(hasher);
        Ok(BlockHeaderHash(hash.0))
    }

    pub fn from_serialized_header(buf: &[u8]) -> BlockHeaderHash {
        let h = Sha512Trunc256Sum::from_data(buf);
        BlockHeaderHash(h.to_bytes())
    }
}

impl BurnchainHeaderHash {
    /// Instantiate a burnchain block hash from a Bitcoin block header
    pub fn from_bitcoin_hash(bitcoin_hash: &Sha256dHash) -> BurnchainHeaderHash {
        // NOTE: Sha256dhash is the same size as BurnchainHeaderHash, so this should never panic
        // Bitcoin stores its hashes in big-endian form, but our codebase stores them in
        // little-endian form (which is also how most libraries work).
        BurnchainHeaderHash::from_bytes_be(bitcoin_hash.as_bytes()).unwrap()
    }

    pub fn to_bitcoin_hash(&self) -> Sha256dHash {
        let bytes = self.0.iter().rev().copied().collect::<Vec<_>>();
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&bytes[0..32]);
        Sha256dHash(buf)
    }

    pub fn zero() -> BurnchainHeaderHash {
        BurnchainHeaderHash([0x00; 32])
    }

    #[cfg(any(test, feature = "testing"))]
    pub fn from_test_data(
        block_height: u64,
        index_root: &TrieHash,
        noise: u64,
    ) -> BurnchainHeaderHash {
        let mut bytes = vec![];
        bytes.extend_from_slice(&block_height.to_be_bytes());
        bytes.extend_from_slice(index_root.as_bytes());
        bytes.extend_from_slice(&noise.to_be_bytes());
        let h = DoubleSha256::from_data(&bytes[..]);
        BurnchainHeaderHash(h.to_bytes())
    }
}

impl StacksMessageCodec for (ConsensusHash, BurnchainHeaderHash) {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.0)?;
        write_next(fd, &self.1)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(
        fd: &mut R,
    ) -> Result<(ConsensusHash, BurnchainHeaderHash), CodecError> {
        let consensus_hash: ConsensusHash = read_next(fd)?;
        let burn_header_hash: BurnchainHeaderHash = read_next(fd)?;
        Ok((consensus_hash, burn_header_hash))
    }
}
