// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2024 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

//! Messages in the signer-miner interaction have a multi-level hierarchy.
//! Signers send messages to each other through Packet messages. These messages,
//! as well as `BlockResponse`, `Transactions`, and `DkgResults` messages are stored
//! StackerDBs based on the `MessageSlotID` for the particular message type. This is a
//! shared identifier space between the four message kinds and their subtypes.
//!
//! These four message kinds are differentiated with a `SignerMessageTypePrefix`
//! and the `SignerMessage` enum.

use std::fmt::{Debug, Display};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::Sender;
use std::sync::Arc;

use blockstack_lib::chainstate::nakamoto::signer_set::NakamotoSigners;
use blockstack_lib::chainstate::nakamoto::NakamotoBlock;
use blockstack_lib::chainstate::stacks::events::StackerDBChunksEvent;
use blockstack_lib::chainstate::stacks::StacksTransaction;
use blockstack_lib::net::api::getinfo::RPCPeerInfoData;
use blockstack_lib::net::api::postblock_proposal::{
    BlockValidateReject, BlockValidateResponse, ValidateRejectCode,
};
use blockstack_lib::util_lib::boot::boot_code_id;
use blockstack_lib::util_lib::signed_structured_data::{
    make_structured_data_domain, structured_data_message_hash,
};
use clarity::consts::{CHAIN_ID_MAINNET, CHAIN_ID_TESTNET};
use clarity::types::chainstate::{
    BlockHeaderHash, ConsensusHash, StacksPrivateKey, StacksPublicKey,
};
use clarity::types::PrivateKey;
use clarity::util::hash::Sha256Sum;
use clarity::util::retry::BoundReader;
use clarity::util::secp256k1::MessageSignature;
use clarity::vm::types::serialization::SerializationError;
use clarity::vm::types::{QualifiedContractIdentifier, TupleData};
use clarity::vm::Value;
use hashbrown::{HashMap, HashSet};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha512_256};
use stacks_common::codec::{
    read_next, read_next_at_most, read_next_exact, write_next, Error as CodecError,
    StacksMessageCodec,
};
use stacks_common::consts::SIGNER_SLOTS_PER_USER;
use stacks_common::util::hash::Sha512Trunc256Sum;
use tiny_http::{
    Method as HttpMethod, Request as HttpRequest, Response as HttpResponse, Server as HttpServer,
};

use crate::http::{decode_http_body, decode_http_request};
use crate::stacks_common::types::PublicKey;
use crate::{
    BlockProposal, EventError, MessageSlotID as MessageSlotIDTrait,
    SignerMessage as SignerMessageTrait, VERSION_STRING,
};

/// Maximum size of the [BlockResponseData] serialized bytes
pub const BLOCK_RESPONSE_DATA_MAX_SIZE: u32 = 2 * 1024 * 1024; // 2MB

define_u8_enum!(
/// Enum representing the stackerdb message identifier: this is
///  the contract index in the signers contracts (i.e., X in signers-0-X)
MessageSlotID {
    /// Block Response message from signers
    BlockResponse = 1
});

define_u8_enum!(
/// Enum representing the slots used by the miner
MinerSlotID {
    /// Block proposal from the miner
    BlockProposal = 0,
    /// Block pushed from the miner
    BlockPushed = 1
});

impl MessageSlotIDTrait for MessageSlotID {
    fn stacker_db_contract(&self, mainnet: bool, reward_cycle: u64) -> QualifiedContractIdentifier {
        NakamotoSigners::make_signers_db_contract_id(reward_cycle, self.to_u32(), mainnet)
    }
    fn all() -> &'static [Self] {
        MessageSlotID::ALL
    }
}

impl SignerMessageTrait<MessageSlotID> for SignerMessage {
    fn msg_id(&self) -> Option<MessageSlotID> {
        self.msg_id()
    }
}

define_u8_enum!(
/// Enum representing the SignerMessage type prefix
SignerMessageTypePrefix {
    /// Block Proposal message from miners
    BlockProposal = 0,
    /// Block Response message from signers
    BlockResponse = 1,
    /// Block Pushed message from miners
    BlockPushed = 2,
    /// Mock block proposal message from Epoch 2.5 miners
    MockProposal = 3,
    /// Mock block signature message from Epoch 2.5 signers
    MockSignature = 4,
    /// Mock block message from Epoch 2.5 miners
    MockBlock = 5
});

#[cfg_attr(test, mutants::skip)]
impl MessageSlotID {
    /// Return the StackerDB contract corresponding to messages of this type
    pub fn stacker_db_contract(
        &self,
        mainnet: bool,
        reward_cycle: u64,
    ) -> QualifiedContractIdentifier {
        NakamotoSigners::make_signers_db_contract_id(reward_cycle, self.to_u32(), mainnet)
    }

    /// Return the u32 identifier for the message slot (used to index the contract that stores it)
    pub fn to_u32(self) -> u32 {
        self.to_u8().into()
    }
}

#[cfg_attr(test, mutants::skip)]
impl Display for MessageSlotID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}({})", self, self.to_u8())
    }
}

impl TryFrom<u8> for SignerMessageTypePrefix {
    type Error = CodecError;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_u8(value).ok_or_else(|| {
            CodecError::DeserializeError(format!("Unknown signer message type prefix: {value}"))
        })
    }
}

impl From<&SignerMessage> for SignerMessageTypePrefix {
    #[cfg_attr(test, mutants::skip)]
    fn from(message: &SignerMessage) -> Self {
        match message {
            SignerMessage::BlockProposal(_) => SignerMessageTypePrefix::BlockProposal,
            SignerMessage::BlockResponse(_) => SignerMessageTypePrefix::BlockResponse,
            SignerMessage::BlockPushed(_) => SignerMessageTypePrefix::BlockPushed,
            SignerMessage::MockProposal(_) => SignerMessageTypePrefix::MockProposal,
            SignerMessage::MockSignature(_) => SignerMessageTypePrefix::MockSignature,
            SignerMessage::MockBlock(_) => SignerMessageTypePrefix::MockBlock,
        }
    }
}

/// The messages being sent through the stacker db contracts
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SignerMessage {
    /// The block proposal from miners for signers to observe and sign
    BlockProposal(BlockProposal),
    /// The block response from signers for miners to observe
    BlockResponse(BlockResponse),
    /// A block pushed from miners to the signers set
    BlockPushed(NakamotoBlock),
    /// A mock signature from the epoch 2.5 signers
    MockSignature(MockSignature),
    /// A mock message from the epoch 2.5 miners
    MockProposal(MockProposal),
    /// A mock block from the epoch 2.5 miners
    MockBlock(MockBlock),
}

impl SignerMessage {
    /// Helper function to determine the slot ID for the provided stacker-db writer id
    ///  Not every message has a `MessageSlotID`: messages from the miner do not
    ///   broadcast over `.signers-0-X` contracts.
    #[cfg_attr(test, mutants::skip)]
    pub fn msg_id(&self) -> Option<MessageSlotID> {
        match self {
            Self::BlockProposal(_)
            | Self::BlockPushed(_)
            | Self::MockProposal(_)
            | Self::MockBlock(_) => None,
            Self::BlockResponse(_) | Self::MockSignature(_) => Some(MessageSlotID::BlockResponse), // Mock signature uses the same slot as block response since its exclusively for epoch 2.5 testing
        }
    }
}

impl StacksMessageCodec for SignerMessage {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        SignerMessageTypePrefix::from(self)
            .to_u8()
            .consensus_serialize(fd)?;
        match self {
            SignerMessage::BlockProposal(block_proposal) => block_proposal.consensus_serialize(fd),
            SignerMessage::BlockResponse(block_response) => block_response.consensus_serialize(fd),
            SignerMessage::BlockPushed(block) => block.consensus_serialize(fd),
            SignerMessage::MockSignature(signature) => signature.consensus_serialize(fd),
            SignerMessage::MockProposal(message) => message.consensus_serialize(fd),
            SignerMessage::MockBlock(block) => block.consensus_serialize(fd),
        }?;
        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let type_prefix_byte = u8::consensus_deserialize(fd)?;
        let type_prefix = SignerMessageTypePrefix::try_from(type_prefix_byte)?;
        let message = match type_prefix {
            SignerMessageTypePrefix::BlockProposal => {
                let block_proposal = StacksMessageCodec::consensus_deserialize(fd)?;
                SignerMessage::BlockProposal(block_proposal)
            }
            SignerMessageTypePrefix::BlockResponse => {
                let block_response = StacksMessageCodec::consensus_deserialize(fd)?;
                SignerMessage::BlockResponse(block_response)
            }
            SignerMessageTypePrefix::BlockPushed => {
                let block = StacksMessageCodec::consensus_deserialize(fd)?;
                SignerMessage::BlockPushed(block)
            }
            SignerMessageTypePrefix::MockProposal => {
                let message = StacksMessageCodec::consensus_deserialize(fd)?;
                SignerMessage::MockProposal(message)
            }
            SignerMessageTypePrefix::MockSignature => {
                let signature = StacksMessageCodec::consensus_deserialize(fd)?;
                SignerMessage::MockSignature(signature)
            }
            SignerMessageTypePrefix::MockBlock => {
                let block = StacksMessageCodec::consensus_deserialize(fd)?;
                SignerMessage::MockBlock(block)
            }
        };
        Ok(message)
    }
}

/// Work around for the fact that a lot of the structs being desierialized are not defined in messages.rs
pub trait StacksMessageCodecExtensions: Sized {
    /// Serialize the struct to the provided writer
    fn inner_consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError>;
    /// Deserialize the struct from the provided reader
    fn inner_consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError>;
}

/// The signer relevant peer information from the stacks node
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PeerInfo {
    /// The burn block height
    pub burn_block_height: u64,
    /// The consensus hash of the stacks tip
    pub stacks_tip_consensus_hash: ConsensusHash,
    /// The stacks tip
    pub stacks_tip: BlockHeaderHash,
    /// The stacks tip height
    pub stacks_tip_height: u64,
    /// The pox consensus
    pub pox_consensus: ConsensusHash,
    /// The server version
    pub server_version: String,
    /// The network id
    pub network_id: u32,
}

impl StacksMessageCodec for PeerInfo {
    #[allow(clippy::needless_as_bytes)] // as_bytes isn't necessary, but verbosity is preferable in the codec impls
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.burn_block_height)?;
        write_next(fd, self.stacks_tip_consensus_hash.as_bytes())?;
        write_next(fd, &self.stacks_tip)?;
        write_next(fd, &self.stacks_tip_height)?;
        write_next(fd, &(self.server_version.as_bytes().len() as u8))?;
        fd.write_all(self.server_version.as_bytes())
            .map_err(CodecError::WriteError)?;
        write_next(fd, &self.pox_consensus)?;
        write_next(fd, &self.network_id)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let burn_block_height = read_next::<u64, _>(fd)?;
        let stacks_tip_consensus_hash = read_next::<ConsensusHash, _>(fd)?;
        let stacks_tip = read_next::<BlockHeaderHash, _>(fd)?;
        let stacks_tip_height = read_next::<u64, _>(fd)?;
        let len_byte: u8 = read_next(fd)?;
        let mut bytes = vec![0u8; len_byte as usize];
        fd.read_exact(&mut bytes).map_err(CodecError::ReadError)?;
        // must encode a valid string
        let server_version = String::from_utf8(bytes).map_err(|_e| {
            CodecError::DeserializeError(
                "Failed to parse server version name: could not contruct from utf8".to_string(),
            )
        })?;
        let pox_consensus = read_next::<ConsensusHash, _>(fd)?;
        let network_id = read_next(fd)?;
        Ok(Self {
            burn_block_height,
            stacks_tip_consensus_hash,
            stacks_tip,
            stacks_tip_height,
            server_version,
            pox_consensus,
            network_id,
        })
    }
}

/// A mock block proposal for Epoch 2.5 mock signing
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MockProposal {
    /// The view of the stacks node peer information at the time of the mock proposal
    pub peer_info: PeerInfo,
    /// The miner's signature across the peer info
    signature: MessageSignature,
}

impl MockProposal {
    /// Create a new mock proposal data struct from the provided peer info, chain id, and private key.
    pub fn new(peer_info: PeerInfo, stacks_private_key: &StacksPrivateKey) -> Self {
        let mut sig = Self {
            signature: MessageSignature::empty(),
            peer_info,
        };
        sig.sign(stacks_private_key)
            .expect("Failed to sign MockProposal");
        sig
    }

    /// The signature hash for the mock proposal
    pub fn miner_signature_hash(&self) -> Sha256Sum {
        let domain_tuple =
            make_structured_data_domain("mock-miner", "1.0.0", self.peer_info.network_id);
        let data_tuple = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "stacks-tip-consensus-hash".into(),
                    Value::buff_from(self.peer_info.stacks_tip_consensus_hash.as_bytes().into())
                        .unwrap(),
                ),
                (
                    "stacks-tip".into(),
                    Value::buff_from(self.peer_info.stacks_tip.as_bytes().into()).unwrap(),
                ),
                (
                    "stacks-tip-height".into(),
                    Value::UInt(self.peer_info.stacks_tip_height.into()),
                ),
                (
                    "server-version".into(),
                    Value::string_ascii_from_bytes(self.peer_info.server_version.clone().into())
                        .unwrap(),
                ),
                (
                    "pox-consensus".into(),
                    Value::buff_from(self.peer_info.pox_consensus.as_bytes().into()).unwrap(),
                ),
            ])
            .expect("Error creating signature hash"),
        );
        structured_data_message_hash(data_tuple, domain_tuple)
    }

    /// The signature hash including the miner's signature. Used by signers.
    fn signer_signature_hash(&self) -> Sha256Sum {
        let domain_tuple =
            make_structured_data_domain("mock-signer", "1.0.0", self.peer_info.network_id);
        let data_tuple = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "miner-signature-hash".into(),
                    Value::buff_from(self.miner_signature_hash().as_bytes().into()).unwrap(),
                ),
                (
                    "miner-signature".into(),
                    Value::buff_from(self.signature.as_bytes().into()).unwrap(),
                ),
            ])
            .expect("Error creating signature hash"),
        );
        structured_data_message_hash(data_tuple, domain_tuple)
    }

    /// Sign the mock proposal and set the internal signature field
    fn sign(&mut self, private_key: &StacksPrivateKey) -> Result<(), String> {
        let signature_hash = self.miner_signature_hash();
        self.signature = private_key.sign(signature_hash.as_bytes())?;
        Ok(())
    }
    /// Verify the mock proposal against the provided miner public key
    pub fn verify(&self, public_key: &StacksPublicKey) -> Result<bool, String> {
        if self.signature == MessageSignature::empty() {
            return Ok(false);
        }
        let signature_hash = self.miner_signature_hash();
        public_key
            .verify(&signature_hash.0, &self.signature)
            .map_err(|e| e.to_string())
    }
}

impl StacksMessageCodec for MockProposal {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        self.peer_info.consensus_serialize(fd)?;
        write_next(fd, &self.signature)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let peer_info = PeerInfo::consensus_deserialize(fd)?;
        let signature = read_next::<MessageSignature, _>(fd)?;
        Ok(Self {
            peer_info,
            signature,
        })
    }
}

/// A mock signature for the stacks node to be used for mock signing.
/// This is only used by Epoch 2.5 signers to simulate the signing of a block for every sortition.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MockSignature {
    /// The signer's signature across the mock proposal
    signature: MessageSignature,
    /// The mock block proposal that was signed across
    pub mock_proposal: MockProposal,
    /// The signature metadata
    pub metadata: SignerMessageMetadata,
}

impl MockSignature {
    /// Create a new mock signature from the provided proposal and signer private key.
    pub fn new(mock_proposal: MockProposal, stacks_private_key: &StacksPrivateKey) -> Self {
        let mut sig = Self {
            signature: MessageSignature::empty(),
            mock_proposal,
            metadata: SignerMessageMetadata::default(),
        };
        sig.sign(stacks_private_key)
            .expect("Failed to sign MockSignature");
        sig
    }

    /// Sign the mock signature and set the internal signature field
    fn sign(&mut self, private_key: &StacksPrivateKey) -> Result<(), String> {
        let signature_hash = self.mock_proposal.signer_signature_hash();
        self.signature = private_key.sign(signature_hash.as_bytes())?;
        Ok(())
    }

    /// Verify the mock signature against the provided signer public key
    pub fn verify(&self, public_key: &StacksPublicKey) -> Result<bool, String> {
        if self.signature == MessageSignature::empty() {
            return Ok(false);
        }
        let signature_hash = self.mock_proposal.signer_signature_hash();
        public_key
            .verify(&signature_hash.0, &self.signature)
            .map_err(|e| e.to_string())
    }
}

impl StacksMessageCodec for MockSignature {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.signature)?;
        self.mock_proposal.consensus_serialize(fd)?;
        self.metadata.consensus_serialize(fd)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let signature = read_next::<MessageSignature, _>(fd)?;
        let mock_proposal = MockProposal::consensus_deserialize(fd)?;
        let metadata = SignerMessageMetadata::consensus_deserialize(fd)?;
        Ok(Self {
            signature,
            mock_proposal,
            metadata,
        })
    }
}

/// The mock block data for epoch 2.5 miners to broadcast to simulate block signing
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MockBlock {
    /// The mock proposal that was signed across
    pub mock_proposal: MockProposal,
    /// The mock signatures that the miner received
    pub mock_signatures: Vec<MockSignature>,
}

impl StacksMessageCodec for MockBlock {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        self.mock_proposal.consensus_serialize(fd)?;
        write_next(fd, &self.mock_signatures)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let mock_proposal = MockProposal::consensus_deserialize(fd)?;
        let mock_signatures = read_next::<Vec<MockSignature>, _>(fd)?;
        Ok(Self {
            mock_proposal,
            mock_signatures,
        })
    }
}

define_u8_enum!(
/// Enum representing the reject code type prefix
RejectCodeTypePrefix {
    /// The block was rejected due to validation issues
    ValidationFailed = 0,
    /// The block was rejected due to connectivity issues with the signer
    ConnectivityIssues = 1,
    /// The block was rejected in a prior round
    RejectedInPriorRound = 2,
    /// The block was rejected due to no sortition view
    NoSortitionView = 3,
    /// The block was rejected due to a mismatch with expected sortition view
    SortitionViewMismatch = 4,
    /// The block was rejected due to a testing directive
    TestingDirective = 5
});

impl TryFrom<u8> for RejectCodeTypePrefix {
    type Error = CodecError;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_u8(value).ok_or_else(|| {
            CodecError::DeserializeError(format!("Unknown reject code type prefix: {value}"))
        })
    }
}

impl From<&RejectCode> for RejectCodeTypePrefix {
    fn from(reject_code: &RejectCode) -> Self {
        match reject_code {
            RejectCode::ValidationFailed(_) => RejectCodeTypePrefix::ValidationFailed,
            RejectCode::ConnectivityIssues(_) => RejectCodeTypePrefix::ConnectivityIssues,
            RejectCode::RejectedInPriorRound => RejectCodeTypePrefix::RejectedInPriorRound,
            RejectCode::NoSortitionView => RejectCodeTypePrefix::NoSortitionView,
            RejectCode::SortitionViewMismatch => RejectCodeTypePrefix::SortitionViewMismatch,
            RejectCode::TestingDirective => RejectCodeTypePrefix::TestingDirective,
        }
    }
}

impl From<&RejectReason> for RejectReasonPrefix {
    fn from(reject_code: &RejectReason) -> Self {
        match reject_code {
            RejectReason::ValidationFailed(_) => RejectReasonPrefix::ValidationFailed,
            RejectReason::ConnectivityIssues(_) => RejectReasonPrefix::ConnectivityIssues,
            RejectReason::RejectedInPriorRound => RejectReasonPrefix::RejectedInPriorRound,
            RejectReason::NoSortitionView => RejectReasonPrefix::NoSortitionView,
            RejectReason::SortitionViewMismatch => RejectReasonPrefix::SortitionViewMismatch,
            RejectReason::TestingDirective => RejectReasonPrefix::TestingDirective,
            RejectReason::ReorgNotAllowed => RejectReasonPrefix::ReorgNotAllowed,
            RejectReason::InvalidBitvec => RejectReasonPrefix::InvalidBitvec,
            RejectReason::PubkeyHashMismatch => RejectReasonPrefix::PubkeyHashMismatch,
            RejectReason::InvalidMiner => RejectReasonPrefix::InvalidMiner,
            RejectReason::NotLatestSortitionWinner => RejectReasonPrefix::NotLatestSortitionWinner,
            RejectReason::InvalidParentBlock => RejectReasonPrefix::InvalidParentBlock,
            RejectReason::DuplicateBlockFound => RejectReasonPrefix::DuplicateBlockFound,
            RejectReason::InvalidTenureExtend => RejectReasonPrefix::InvalidTenureExtend,
            RejectReason::Unknown(_) => RejectReasonPrefix::Unknown,
            RejectReason::NotRejected => RejectReasonPrefix::NotRejected,
        }
    }
}

/// This enum is used to supply a `reason_code` for block rejections
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RejectCode {
    /// RPC endpoint Validation failed
    ValidationFailed(ValidateRejectCode),
    /// No Sortition View to verify against
    NoSortitionView,
    /// The block was rejected due to connectivity issues with the signer
    ConnectivityIssues(String),
    /// The block was rejected in a prior round
    RejectedInPriorRound,
    /// The block was rejected due to a mismatch with expected sortition view
    SortitionViewMismatch,
    /// The block was rejected due to a testing directive
    TestingDirective,
}

impl From<&RejectReason> for RejectCode {
    fn from(reject_reason: &RejectReason) -> Self {
        match reject_reason {
            RejectReason::ValidationFailed(code) => RejectCode::ValidationFailed(*code),
            RejectReason::NoSortitionView => RejectCode::NoSortitionView,
            RejectReason::ConnectivityIssues(reason) => {
                RejectCode::ConnectivityIssues(reason.clone())
            }
            RejectReason::RejectedInPriorRound => RejectCode::RejectedInPriorRound,
            RejectReason::SortitionViewMismatch => RejectCode::SortitionViewMismatch,
            RejectReason::TestingDirective => RejectCode::TestingDirective,
            // Newer reject reasons were expanded from SortitionViewMismatch
            _ => RejectCode::SortitionViewMismatch,
        }
    }
}

/// This enum is used to supply a `reason_code` in the block response data
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RejectReason {
    /// RPC endpoint Validation failed
    ValidationFailed(ValidateRejectCode),
    /// No Sortition View to verify against
    NoSortitionView,
    /// The block was rejected due to connectivity issues with the signer
    ConnectivityIssues(String),
    /// The block was rejected in a prior round
    RejectedInPriorRound,
    /// The block was rejected due to a mismatch with expected sortition view
    SortitionViewMismatch,
    /// The block was rejected due to a testing directive
    TestingDirective,
    /// The block attempted to reorg the previous tenure but was not allowed
    ReorgNotAllowed,
    /// The bitvec field does not match what is expected
    InvalidBitvec,
    /// The miner's pubkey hash does not match the winning pubkey hash
    PubkeyHashMismatch,
    /// The miner has been marked as invalid
    InvalidMiner,
    /// Miner is last sortition winner, when the current sortition winner is
    /// still valid
    NotLatestSortitionWinner,
    /// The block does not confirm the expected parent block
    InvalidParentBlock,
    /// The block contains a block found tenure change, but we've already seen
    /// a block found
    DuplicateBlockFound,
    /// The block attempted a tenure extend but the burn view has not changed
    /// and not enough time has passed for a time-based tenure extend
    InvalidTenureExtend,
    /// The block was approved, no rejection details needed
    NotRejected,
    /// Handle unknown codes gracefully
    Unknown(u8),
}

/// Enum representing the reject details type prefix
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum RejectReasonPrefix {
    /// The block was rejected due to validation issues
    ValidationFailed = 0,
    /// The block was rejected due to connectivity issues with the signer
    ConnectivityIssues = 1,
    /// The block was rejected in a prior round
    RejectedInPriorRound = 2,
    /// The block was rejected due to no sortition view
    NoSortitionView = 3,
    /// The block was rejected due to a mismatch with expected sortition view
    SortitionViewMismatch = 4,
    /// The block was rejected due to a testing directive
    TestingDirective = 5,
    /// The block attempted to reorg the previous tenure but was not allowed
    ReorgNotAllowed = 6,
    /// The bitvec field does not match what is expected
    InvalidBitvec = 7,
    /// The miner's pubkey hash does not match the winning pubkey hash
    PubkeyHashMismatch = 8,
    /// The miner has been marked as invalid
    InvalidMiner = 9,
    /// Miner is last sortition winner, when the current sortition winner is
    /// still valid
    NotLatestSortitionWinner = 10,
    /// The block does not confirm the expected parent block
    InvalidParentBlock = 11,
    /// The block contains a block found tenure change, but we've already seen
    /// a block found
    DuplicateBlockFound = 12,
    /// The block attempted a tenure extend but the burn view has not changed
    /// and not enough time has passed for a time-based tenure extend
    InvalidTenureExtend = 13,
    /// Unknown reject code, for forward compatibility
    Unknown = 254,
    /// The block was approved, no rejection details needed
    NotRejected = 255,
}

impl RejectReasonPrefix {
    /// Convert to a u8 representation
    pub fn to_u8(&self) -> u8 {
        match self {
            Self::ValidationFailed => 0,
            Self::ConnectivityIssues => 1,
            Self::RejectedInPriorRound => 2,
            Self::NoSortitionView => 3,
            Self::SortitionViewMismatch => 4,
            Self::TestingDirective => 5,
            Self::ReorgNotAllowed => 6,
            Self::InvalidBitvec => 7,
            Self::PubkeyHashMismatch => 8,
            Self::InvalidMiner => 9,
            Self::NotLatestSortitionWinner => 10,
            Self::InvalidParentBlock => 11,
            Self::DuplicateBlockFound => 12,
            Self::InvalidTenureExtend => 13,
            Self::Unknown => 254,
            Self::NotRejected => 255,
        }
    }
}

impl From<u8> for RejectReasonPrefix {
    fn from(v: u8) -> Self {
        match v {
            0 => Self::ValidationFailed,
            1 => Self::ConnectivityIssues,
            2 => Self::RejectedInPriorRound,
            3 => Self::NoSortitionView,
            4 => Self::SortitionViewMismatch,
            5 => Self::TestingDirective,
            6 => Self::ReorgNotAllowed,
            7 => Self::InvalidBitvec,
            8 => Self::PubkeyHashMismatch,
            9 => Self::InvalidMiner,
            10 => Self::NotLatestSortitionWinner,
            11 => Self::InvalidParentBlock,
            12 => Self::DuplicateBlockFound,
            13 => Self::InvalidTenureExtend,
            255 => Self::NotRejected,
            // For forward compatibility, all other values are unknown
            _ => Self::Unknown,
        }
    }
}

impl From<&RejectCode> for RejectReason {
    fn from(reject_code: &RejectCode) -> Self {
        match reject_code {
            RejectCode::ValidationFailed(code) => RejectReason::ValidationFailed(*code),
            RejectCode::ConnectivityIssues(reason) => {
                RejectReason::ConnectivityIssues(reason.clone())
            }
            RejectCode::RejectedInPriorRound => RejectReason::RejectedInPriorRound,
            RejectCode::NoSortitionView => RejectReason::NoSortitionView,
            RejectCode::SortitionViewMismatch => RejectReason::SortitionViewMismatch,
            RejectCode::TestingDirective => RejectReason::TestingDirective,
        }
    }
}

define_u8_enum!(
/// Enum representing the BlockResponse type prefix
BlockResponseTypePrefix {
    /// An accepted block response
    Accepted = 0,
    /// A rejected block response
    Rejected = 1
});

impl TryFrom<u8> for BlockResponseTypePrefix {
    type Error = CodecError;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_u8(value).ok_or_else(|| {
            CodecError::DeserializeError(format!("Unknown block response type prefix: {value}"))
        })
    }
}

impl From<&BlockResponse> for BlockResponseTypePrefix {
    fn from(block_response: &BlockResponse) -> Self {
        match block_response {
            BlockResponse::Accepted(_) => BlockResponseTypePrefix::Accepted,
            BlockResponse::Rejected(_) => BlockResponseTypePrefix::Rejected,
        }
    }
}

/// The response that a signer sends back to observing miners
/// either accepting or rejecting a Nakamoto block with the corresponding reason
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum BlockResponse {
    /// The Nakamoto block was accepted and therefore signed
    Accepted(BlockAccepted),
    /// The Nakamoto block was rejected and therefore not signed
    Rejected(BlockRejection),
}

#[cfg_attr(test, mutants::skip)]
impl std::fmt::Display for BlockResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlockResponse::Accepted(a) => {
                write!(
                    f,
                    "BlockAccepted: signer_sighash = {}, signature = {}, version = {}",
                    a.signer_signature_hash, a.signature, a.metadata.server_version
                )
            }
            BlockResponse::Rejected(r) => {
                write!(
                    f,
                    "BlockRejected: signer_sighash = {}, code = {}, reason = {}, signature = {}, version = {}",
                    r.reason_code, r.reason, r.signer_signature_hash, r.signature, r.metadata.server_version
                )
            }
        }
    }
}

impl BlockResponse {
    /// Create a new accepted BlockResponse for the provided block signer signature hash and signature
    pub fn accepted(
        signer_signature_hash: Sha512Trunc256Sum,
        signature: MessageSignature,
        tenure_extend_timestamp: u64,
    ) -> Self {
        Self::Accepted(BlockAccepted {
            signer_signature_hash,
            signature,
            metadata: SignerMessageMetadata::default(),
            response_data: BlockResponseData::new(
                tenure_extend_timestamp,
                RejectReason::NotRejected,
            ),
        })
    }

    /// Create a new rejected BlockResponse for the provided block signer signature hash and rejection code and sign it with the provided private key
    pub fn rejected(
        hash: Sha512Trunc256Sum,
        reject_reason: RejectReason,
        private_key: &StacksPrivateKey,
        mainnet: bool,
        timestamp: u64,
    ) -> Self {
        Self::Rejected(BlockRejection::new(
            hash,
            reject_reason,
            private_key,
            mainnet,
            timestamp,
        ))
    }

    /// Get the tenure extend timestamp from the block response
    pub fn get_tenure_extend_timestamp(&self) -> u64 {
        match self {
            BlockResponse::Accepted(accepted) => accepted.response_data.tenure_extend_timestamp,
            BlockResponse::Rejected(rejection) => rejection.response_data.tenure_extend_timestamp,
        }
    }

    /// Get the signer signature hash from the block response
    pub fn get_signer_signature_hash(&self) -> Sha512Trunc256Sum {
        match self {
            BlockResponse::Accepted(accepted) => accepted.signer_signature_hash,
            BlockResponse::Rejected(rejection) => rejection.signer_signature_hash,
        }
    }

    /// The signer signature hash for the block response
    pub fn signer_signature_hash(&self) -> Sha512Trunc256Sum {
        match self {
            BlockResponse::Accepted(accepted) => accepted.signer_signature_hash,
            BlockResponse::Rejected(rejection) => rejection.signer_signature_hash,
        }
    }

    /// Get the block accept data from the block response
    pub fn as_block_accepted(&self) -> Option<&BlockAccepted> {
        match self {
            BlockResponse::Accepted(accepted) => Some(accepted),
            _ => None,
        }
    }

    /// Get the block accept data from the block response
    pub fn as_block_rejection(&self) -> Option<&BlockRejection> {
        match self {
            BlockResponse::Rejected(rejection) => Some(rejection),
            _ => None,
        }
    }
}

impl StacksMessageCodec for BlockResponse {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &(BlockResponseTypePrefix::from(self) as u8))?;
        match self {
            BlockResponse::Accepted(accepted) => {
                write_next(fd, accepted)?;
            }
            BlockResponse::Rejected(rejection) => {
                write_next(fd, rejection)?;
            }
        };
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let type_prefix_byte = read_next::<u8, _>(fd)?;
        let type_prefix = BlockResponseTypePrefix::try_from(type_prefix_byte)?;
        let response = match type_prefix {
            BlockResponseTypePrefix::Accepted => {
                let accepted = read_next::<BlockAccepted, _>(fd)?;
                BlockResponse::Accepted(accepted)
            }
            BlockResponseTypePrefix::Rejected => {
                let rejection = read_next::<BlockRejection, _>(fd)?;
                BlockResponse::Rejected(rejection)
            }
        };
        Ok(response)
    }
}

/// Metadata for signer messages
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SignerMessageMetadata {
    /// The signer's server version
    pub server_version: String,
}

/// To ensure backwards compatibility, when deserializing,
/// if no bytes are found, return empty metadata
impl StacksMessageCodec for SignerMessageMetadata {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.server_version.as_bytes().to_vec())?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        match read_next::<Vec<u8>, _>(fd) {
            Ok(server_version) => {
                let server_version = String::from_utf8(server_version).map_err(|e| {
                    CodecError::DeserializeError(format!(
                        "Failed to decode server version: {:?}",
                        &e
                    ))
                })?;
                Ok(Self { server_version })
            }
            Err(_) => {
                // For backwards compatibility, return empty metadata
                Ok(Self::empty())
            }
        }
    }
}

impl Default for SignerMessageMetadata {
    fn default() -> Self {
        Self {
            server_version: VERSION_STRING.to_string(),
        }
    }
}

impl SignerMessageMetadata {
    /// Empty metadata
    pub fn empty() -> Self {
        Self {
            server_version: String::new(),
        }
    }
}

/// The latest version of the block response data
pub const BLOCK_RESPONSE_DATA_VERSION: u8 = 3;

/// Versioned, backwards-compatible struct for block response data
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BlockResponseData {
    /// The version of the block response data
    pub version: u8,
    /// The block response data
    pub tenure_extend_timestamp: u64,
    /// Block rejection reason
    pub reject_reason: RejectReason,
    /// When deserializing future versions,
    /// there may be extra bytes that we don't know about
    pub unknown_bytes: Vec<u8>,
}

impl BlockResponseData {
    /// Create a new BlockResponseData for the provided tenure extend timestamp and unknown bytes
    pub fn new(tenure_extend_timestamp: u64, reject_reason: RejectReason) -> Self {
        Self {
            version: BLOCK_RESPONSE_DATA_VERSION,
            tenure_extend_timestamp,
            reject_reason,
            unknown_bytes: vec![],
        }
    }

    /// Create an empty BlockResponseData
    pub fn empty() -> Self {
        Self::new(u64::MAX, RejectReason::NotRejected)
    }

    /// Serialize the "inner" block response data. Used to determine the bytes length of the serialized block response data
    fn inner_consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.tenure_extend_timestamp)?;
        write_next(fd, &self.reject_reason)?;
        fd.write_all(&self.unknown_bytes)
            .map_err(CodecError::WriteError)?;
        Ok(())
    }
}

impl StacksMessageCodec for BlockResponseData {
    /// Serialize the block response data.
    /// When creating a new version of the block response data, we are only ever
    /// appending new bytes to the end of the struct. When serializing, we use
    /// `bytes_len` to ensure that older versions of the code can read through the
    /// end of the serialized bytes.
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.version)?;
        let mut inner_bytes = vec![];
        self.inner_consensus_serialize(&mut inner_bytes)?;
        write_next(fd, &inner_bytes)?;
        Ok(())
    }

    /// Deserialize the block response data in a backwards-compatible manner.
    /// When creating a new version of the block response data, we are only ever
    /// appending new bytes to the end of the struct. When deserializing, we use
    /// `bytes_len` to ensure that we read through the end of the serialized bytes.
    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let Ok(version) = read_next(fd) else {
            return Ok(Self::empty());
        };
        let inner_bytes: Vec<u8> = read_next_at_most(fd, BLOCK_RESPONSE_DATA_MAX_SIZE)?;
        let mut inner_reader = inner_bytes.as_slice();
        let tenure_extend_timestamp = read_next(&mut inner_reader)?;
        let reject_reason = read_next::<RejectReason, _>(&mut inner_reader)?;
        Ok(Self {
            version,
            tenure_extend_timestamp,
            reject_reason,
            unknown_bytes: inner_reader.to_vec(),
        })
    }
}

/// A rejection response from a signer for a proposed block
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BlockAccepted {
    /// The signer signature hash of the block that was accepted
    pub signer_signature_hash: Sha512Trunc256Sum,
    /// The signer's signature across the acceptance
    pub signature: MessageSignature,
    /// Signer message metadata
    pub metadata: SignerMessageMetadata,
    /// Extra versioned block response data
    pub response_data: BlockResponseData,
}

impl StacksMessageCodec for BlockAccepted {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.signer_signature_hash)?;
        write_next(fd, &self.signature)?;
        write_next(fd, &self.metadata)?;
        write_next(fd, &self.response_data)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let signer_signature_hash = read_next::<Sha512Trunc256Sum, _>(fd)?;
        let signature = read_next::<MessageSignature, _>(fd)?;
        let metadata = read_next::<SignerMessageMetadata, _>(fd)?;
        let response_data = read_next::<BlockResponseData, _>(fd)?;
        Ok(Self {
            signer_signature_hash,
            signature,
            metadata,
            response_data,
        })
    }
}

impl BlockAccepted {
    /// Create a new BlockAccepted for the provided block signer signature hash and signature
    pub fn new(
        signer_signature_hash: Sha512Trunc256Sum,
        signature: MessageSignature,
        tenure_extend_timestamp: u64,
    ) -> Self {
        Self {
            signer_signature_hash,
            signature,
            metadata: SignerMessageMetadata::default(),
            response_data: BlockResponseData::new(
                tenure_extend_timestamp,
                RejectReason::NotRejected,
            ),
        }
    }
}

/// A rejection response from a signer for a proposed block
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BlockRejection {
    /// The reason for the rejection
    pub reason: String,
    /// The reason code for the rejection
    pub reason_code: RejectCode,
    /// The signer signature hash of the block that was rejected
    pub signer_signature_hash: Sha512Trunc256Sum,
    /// The signer's signature across the rejection
    pub signature: MessageSignature,
    /// The chain id
    pub chain_id: u32,
    /// Signer message metadata
    pub metadata: SignerMessageMetadata,
    /// Extra versioned block response data
    pub response_data: BlockResponseData,
}

impl BlockRejection {
    /// Create a new BlockRejection for the provided block and reason code
    pub fn new(
        signer_signature_hash: Sha512Trunc256Sum,
        reject_reason: RejectReason,
        private_key: &StacksPrivateKey,
        mainnet: bool,
        timestamp: u64,
    ) -> Self {
        let chain_id = if mainnet {
            CHAIN_ID_MAINNET
        } else {
            CHAIN_ID_TESTNET
        };
        let mut rejection = Self {
            reason: reject_reason.to_string(),
            reason_code: (&reject_reason).into(),
            signer_signature_hash,
            signature: MessageSignature::empty(),
            chain_id,
            metadata: SignerMessageMetadata::default(),
            response_data: BlockResponseData::new(timestamp, reject_reason),
        };
        rejection
            .sign(private_key)
            .expect("Failed to sign BlockRejection");
        rejection
    }

    /// Create a new BlockRejection from a BlockValidateRejection
    pub fn from_validate_rejection(
        reject: BlockValidateReject,
        private_key: &StacksPrivateKey,
        mainnet: bool,
        timestamp: u64,
    ) -> Self {
        let chain_id = if mainnet {
            CHAIN_ID_MAINNET
        } else {
            CHAIN_ID_TESTNET
        };
        let reject_code = RejectCode::ValidationFailed(reject.reason_code);
        let mut rejection = Self {
            reason: reject.reason,
            reason_code: reject_code.clone(),
            signer_signature_hash: reject.signer_signature_hash,
            chain_id,
            signature: MessageSignature::empty(),
            metadata: SignerMessageMetadata::default(),
            response_data: BlockResponseData::new(timestamp, (&reject_code).into()),
        };
        rejection
            .sign(private_key)
            .expect("Failed to sign BlockRejection");
        rejection
    }

    /// The signature hash for the block rejection
    pub fn hash(&self) -> Sha256Sum {
        let domain_tuple = make_structured_data_domain("block-rejection", "1.0.0", self.chain_id);
        let data = Value::buff_from(self.signer_signature_hash.as_bytes().into()).unwrap();
        structured_data_message_hash(data, domain_tuple)
    }

    /// Sign the block rejection and set the internal signature field
    fn sign(&mut self, private_key: &StacksPrivateKey) -> Result<(), String> {
        let signature_hash = self.hash();
        self.signature = private_key.sign(signature_hash.as_bytes())?;
        Ok(())
    }

    /// Verify the rejection's signature against the provided signer public key
    pub fn verify(&self, public_key: &StacksPublicKey) -> Result<bool, String> {
        if self.signature == MessageSignature::empty() {
            return Ok(false);
        }
        let signature_hash = self.hash();
        public_key
            .verify(&signature_hash.0, &self.signature)
            .map_err(|e| e.to_string())
    }

    /// Recover the public key from the rejection signature
    pub fn recover_public_key(&self) -> Result<StacksPublicKey, &'static str> {
        if self.signature == MessageSignature::empty() {
            return Err("No signature to recover public key from");
        }
        let signature_hash = self.hash();
        StacksPublicKey::recover_to_pubkey(signature_hash.as_bytes(), &self.signature)
    }
}

impl StacksMessageCodec for BlockRejection {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.reason.as_bytes().to_vec())?;
        write_next(fd, &self.reason_code)?;
        write_next(fd, &self.signer_signature_hash)?;
        write_next(fd, &self.chain_id)?;
        write_next(fd, &self.signature)?;
        write_next(fd, &self.metadata)?;
        write_next(fd, &self.response_data)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let reason_bytes = read_next::<Vec<u8>, _>(fd)?;
        let reason = String::from_utf8(reason_bytes).map_err(|e| {
            CodecError::DeserializeError(format!("Failed to decode reason string: {:?}", &e))
        })?;
        let reason_code = read_next::<RejectCode, _>(fd)?;
        let signer_signature_hash = read_next::<Sha512Trunc256Sum, _>(fd)?;
        let chain_id = read_next::<u32, _>(fd)?;
        let signature = read_next::<MessageSignature, _>(fd)?;
        let metadata = read_next::<SignerMessageMetadata, _>(fd)?;
        let response_data = read_next::<BlockResponseData, _>(fd)?;
        Ok(Self {
            reason,
            reason_code,
            signer_signature_hash,
            chain_id,
            signature,
            metadata,
            response_data,
        })
    }
}

impl StacksMessageCodec for RejectCode {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &(RejectCodeTypePrefix::from(self) as u8))?;
        // Do not do a single match here as we may add other variants in the future and don't want to miss adding it
        match self {
            RejectCode::ValidationFailed(code) => write_next(fd, &(*code as u8))?,
            RejectCode::ConnectivityIssues(_)
            | RejectCode::RejectedInPriorRound
            | RejectCode::NoSortitionView
            | RejectCode::SortitionViewMismatch
            | RejectCode::TestingDirective => {
                // No additional data to serialize / deserialize
            }
        };
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let type_prefix_byte = read_next::<u8, _>(fd)?;
        let type_prefix = RejectCodeTypePrefix::try_from(type_prefix_byte)?;
        let code = match type_prefix {
            RejectCodeTypePrefix::ValidationFailed => RejectCode::ValidationFailed(
                ValidateRejectCode::try_from(read_next::<u8, _>(fd)?).map_err(|e| {
                    CodecError::DeserializeError(format!(
                        "Failed to decode validation reject code: {:?}",
                        &e
                    ))
                })?,
            ),
            RejectCodeTypePrefix::ConnectivityIssues => {
                RejectCode::ConnectivityIssues("unspecified".to_string())
            }
            RejectCodeTypePrefix::RejectedInPriorRound => RejectCode::RejectedInPriorRound,
            RejectCodeTypePrefix::NoSortitionView => RejectCode::NoSortitionView,
            RejectCodeTypePrefix::SortitionViewMismatch => RejectCode::SortitionViewMismatch,
            RejectCodeTypePrefix::TestingDirective => RejectCode::TestingDirective,
        };
        Ok(code)
    }
}

impl StacksMessageCodec for RejectReason {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &(RejectReasonPrefix::from(self) as u8))?;
        // Do not do a single match here as we may add other variants in the future and don't want to miss adding it
        match self {
            RejectReason::ValidationFailed(code) => write_next(fd, &(*code as u8))?,
            RejectReason::ConnectivityIssues(_)
            | RejectReason::RejectedInPriorRound
            | RejectReason::NoSortitionView
            | RejectReason::SortitionViewMismatch
            | RejectReason::TestingDirective
            | RejectReason::ReorgNotAllowed
            | RejectReason::InvalidBitvec
            | RejectReason::PubkeyHashMismatch
            | RejectReason::InvalidMiner
            | RejectReason::NotLatestSortitionWinner
            | RejectReason::InvalidParentBlock
            | RejectReason::DuplicateBlockFound
            | RejectReason::InvalidTenureExtend
            | RejectReason::Unknown(_)
            | RejectReason::NotRejected => {
                // No additional data to serialize / deserialize
            }
        };
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
        let type_prefix_byte = read_next::<u8, _>(fd)?;
        let type_prefix = RejectReasonPrefix::from(type_prefix_byte);
        let code = match type_prefix {
            RejectReasonPrefix::ValidationFailed => RejectReason::ValidationFailed(
                ValidateRejectCode::try_from(read_next::<u8, _>(fd)?).map_err(|e| {
                    CodecError::DeserializeError(format!(
                        "Failed to decode validation reject code: {:?}",
                        &e
                    ))
                })?,
            ),
            RejectReasonPrefix::ConnectivityIssues => {
                RejectReason::ConnectivityIssues("unspecified".to_string())
            }
            RejectReasonPrefix::RejectedInPriorRound => RejectReason::RejectedInPriorRound,
            RejectReasonPrefix::NoSortitionView => RejectReason::NoSortitionView,
            RejectReasonPrefix::SortitionViewMismatch => RejectReason::SortitionViewMismatch,
            RejectReasonPrefix::TestingDirective => RejectReason::TestingDirective,
            RejectReasonPrefix::ReorgNotAllowed => RejectReason::ReorgNotAllowed,
            RejectReasonPrefix::InvalidBitvec => RejectReason::InvalidBitvec,
            RejectReasonPrefix::PubkeyHashMismatch => RejectReason::PubkeyHashMismatch,
            RejectReasonPrefix::InvalidMiner => RejectReason::InvalidMiner,
            RejectReasonPrefix::NotLatestSortitionWinner => RejectReason::NotLatestSortitionWinner,
            RejectReasonPrefix::InvalidParentBlock => RejectReason::InvalidParentBlock,
            RejectReasonPrefix::DuplicateBlockFound => RejectReason::DuplicateBlockFound,
            RejectReasonPrefix::InvalidTenureExtend => RejectReason::InvalidTenureExtend,
            RejectReasonPrefix::Unknown => RejectReason::Unknown(type_prefix_byte),
            RejectReasonPrefix::NotRejected => RejectReason::NotRejected,
        };
        Ok(code)
    }
}

#[cfg_attr(test, mutants::skip)]
impl std::fmt::Display for RejectCode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RejectCode::ValidationFailed(code) => write!(f, "Validation failed: {:?}", code),
            RejectCode::ConnectivityIssues(reason) => write!(
                f,
                "The block was rejected due to connectivity issues with the signer: {reason}"
            ),
            RejectCode::RejectedInPriorRound => write!(
                f,
                "The block was proposed before and rejected by the signer."
            ),
            RejectCode::NoSortitionView => {
                write!(f, "The block was rejected due to no sortition view.")
            }
            RejectCode::SortitionViewMismatch => {
                write!(
                    f,
                    "The block was rejected due to a mismatch with expected sortition view."
                )
            }
            RejectCode::TestingDirective => {
                write!(f, "The block was rejected due to a testing directive.")
            }
        }
    }
}

#[cfg_attr(test, mutants::skip)]
impl std::fmt::Display for RejectReason {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RejectReason::ValidationFailed(code) => write!(f, "Validation failed: {:?}", code),
            RejectReason::ConnectivityIssues(reason) => write!(
                f,
                "The block was rejected due to connectivity issues with the signer: {reason}"
            ),
            RejectReason::RejectedInPriorRound => write!(
                f,
                "The block was proposed before and rejected by the signer."
            ),
            RejectReason::NoSortitionView => {
                write!(f, "The block was rejected due to no sortition view.")
            }
            RejectReason::SortitionViewMismatch => {
                write!(
                    f,
                    "The block was rejected due to a mismatch with expected sortition view."
                )
            }
            RejectReason::TestingDirective => {
                write!(f, "The block was rejected due to a testing directive.")
            }
            RejectReason::ReorgNotAllowed => {
                write!(
                    f,
                    "The block attempted to reorg the previous tenure(s) but was not allowed."
                )
            }
            RejectReason::InvalidBitvec => {
                write!(f, "The bitvec field does not match what is expected.")
            }
            RejectReason::PubkeyHashMismatch => {
                write!(
                    f,
                    "The miner's pubkey hash does not match the winning pubkey hash."
                )
            }
            RejectReason::InvalidMiner => {
                write!(f, "The miner has been marked as invalid.")
            }
            RejectReason::NotLatestSortitionWinner => {
                write!(
                    f,
                    "Miner is last sortition winner, when the current sortition winner is still valid."
                )
            }
            RejectReason::InvalidParentBlock => {
                write!(f, "The block does not confirm the expected parent block.")
            }
            RejectReason::DuplicateBlockFound => {
                write!(
                    f,
                    "The block contains a block found tenure change, but we've already seen a block found."
                )
            }
            RejectReason::InvalidTenureExtend => {
                write!(
                    f,
                    "The block attempted a tenure extend but the burn view has not changed and not enough time has passed for a time-based tenure extend."
                )
            }
            RejectReason::Unknown(code) => {
                write!(f, "Unknown reject code: {}", code)
            }
            RejectReason::NotRejected => {
                write!(f, "The block was approved, no rejection details needed.")
            }
        }
    }
}

impl From<BlockResponse> for SignerMessage {
    fn from(block_response: BlockResponse) -> Self {
        Self::BlockResponse(block_response)
    }
}

#[cfg(test)]
mod test {
    use blockstack_lib::chainstate::nakamoto::NakamotoBlockHeader;
    use blockstack_lib::chainstate::stacks::{
        TransactionAnchorMode, TransactionAuth, TransactionPayload, TransactionPostConditionMode,
        TransactionSmartContract, TransactionVersion,
    };
    use blockstack_lib::util_lib::strings::StacksString;
    use clarity::consts::CHAIN_ID_MAINNET;
    use clarity::types::chainstate::{ConsensusHash, StacksBlockId, TrieHash};
    use clarity::types::PrivateKey;
    use clarity::util::hash::{hex_bytes, MerkleTree};
    use clarity::util::secp256k1::MessageSignature;
    use rand::rngs::mock;
    use rand::{thread_rng, Rng, RngCore};
    use rand_core::OsRng;
    use stacks_common::bitvec::BitVec;
    use stacks_common::consts::CHAIN_ID_TESTNET;
    use stacks_common::types::chainstate::StacksPrivateKey;

    use super::{StacksMessageCodecExtensions, *};
    use crate::events::BlockProposalData;

    #[test]
    fn signer_slots_count_is_sane() {
        let slot_identifiers_len = MessageSlotID::ALL.len();
        assert!(
            SIGNER_SLOTS_PER_USER as usize >= slot_identifiers_len,
            "stacks_common::SIGNER_SLOTS_PER_USER ({}) must be >= slot identifiers ({})",
            SIGNER_SLOTS_PER_USER,
            slot_identifiers_len,
        );
    }

    #[test]
    fn serde_reject_code() {
        let code = RejectCode::ValidationFailed(ValidateRejectCode::InvalidBlock);
        let serialized_code = code.serialize_to_vec();
        let deserialized_code = read_next::<RejectCode, _>(&mut &serialized_code[..])
            .expect("Failed to deserialize RejectCode");
        assert_eq!(code, deserialized_code);

        let code = RejectCode::ConnectivityIssues("unspecified".to_string());
        let serialized_code = code.serialize_to_vec();
        let deserialized_code = read_next::<RejectCode, _>(&mut &serialized_code[..])
            .expect("Failed to deserialize RejectCode");
        assert_eq!(code, deserialized_code);
    }

    #[test]
    fn serde_block_rejection() {
        let rejection = BlockRejection::new(
            Sha512Trunc256Sum([0u8; 32]),
            RejectReason::ValidationFailed(ValidateRejectCode::InvalidBlock),
            &StacksPrivateKey::random(),
            thread_rng().gen_bool(0.5),
            thread_rng().next_u64(),
        );
        let serialized_rejection = rejection.serialize_to_vec();
        let deserialized_rejection = read_next::<BlockRejection, _>(&mut &serialized_rejection[..])
            .expect("Failed to deserialize BlockRejection");
        assert_eq!(rejection, deserialized_rejection);

        let rejection = BlockRejection::new(
            Sha512Trunc256Sum([1u8; 32]),
            RejectReason::ConnectivityIssues("unspecified".to_string()),
            &StacksPrivateKey::random(),
            thread_rng().gen_bool(0.5),
            thread_rng().next_u64(),
        );
        let serialized_rejection = rejection.serialize_to_vec();
        let deserialized_rejection = read_next::<BlockRejection, _>(&mut &serialized_rejection[..])
            .expect("Failed to deserialize BlockRejection");
        assert_eq!(rejection, deserialized_rejection);
    }

    #[test]
    fn serde_block_response() {
        let accepted = BlockAccepted {
            signer_signature_hash: Sha512Trunc256Sum([0u8; 32]),
            signature: MessageSignature::empty(),
            metadata: SignerMessageMetadata::default(),
            response_data: BlockResponseData::new(
                thread_rng().next_u64(),
                RejectReason::NotRejected,
            ),
        };
        let response = BlockResponse::Accepted(accepted);
        let serialized_response = response.serialize_to_vec();
        let deserialized_response = read_next::<BlockResponse, _>(&mut &serialized_response[..])
            .expect("Failed to deserialize BlockResponse");
        assert_eq!(response, deserialized_response);

        let response = BlockResponse::Rejected(BlockRejection::new(
            Sha512Trunc256Sum([1u8; 32]),
            RejectReason::ValidationFailed(ValidateRejectCode::InvalidBlock),
            &StacksPrivateKey::random(),
            thread_rng().gen_bool(0.5),
            thread_rng().next_u64(),
        ));
        let serialized_response = response.serialize_to_vec();
        let deserialized_response = read_next::<BlockResponse, _>(&mut &serialized_response[..])
            .expect("Failed to deserialize BlockResponse");
        assert_eq!(response, deserialized_response);
    }

    #[test]
    fn serde_signer_message() {
        let accepted = BlockAccepted {
            signer_signature_hash: Sha512Trunc256Sum([2u8; 32]),
            signature: MessageSignature::empty(),
            metadata: SignerMessageMetadata::default(),
            response_data: BlockResponseData::new(
                thread_rng().next_u64(),
                RejectReason::NotRejected,
            ),
        };
        let signer_message = SignerMessage::BlockResponse(BlockResponse::Accepted(accepted));
        let serialized_signer_message = signer_message.serialize_to_vec();
        let deserialized_signer_message =
            read_next::<SignerMessage, _>(&mut &serialized_signer_message[..])
                .expect("Failed to deserialize SignerMessage");
        assert_eq!(signer_message, deserialized_signer_message);

        let header = NakamotoBlockHeader::empty();
        let mut block = NakamotoBlock {
            header,
            txs: vec![],
        };
        let tx_merkle_root = {
            let txid_vecs: Vec<_> = block
                .txs
                .iter()
                .map(|tx| tx.txid().as_bytes().to_vec())
                .collect();

            MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs).root()
        };
        block.header.tx_merkle_root = tx_merkle_root;

        let block_proposal = BlockProposal {
            block,
            burn_height: thread_rng().next_u64(),
            reward_cycle: thread_rng().next_u64(),
            block_proposal_data: BlockProposalData::empty(),
        };
        let signer_message = SignerMessage::BlockProposal(block_proposal);
        let serialized_signer_message = signer_message.serialize_to_vec();
        let deserialized_signer_message =
            read_next::<SignerMessage, _>(&mut &serialized_signer_message[..])
                .expect("Failed to deserialize SignerMessage");
        assert_eq!(signer_message, deserialized_signer_message);
    }

    fn random_peer_data() -> PeerInfo {
        let burn_block_height = thread_rng().next_u64();
        let stacks_tip_consensus_byte: u8 = thread_rng().gen();
        let stacks_tip_byte: u8 = thread_rng().gen();
        let stacks_tip_height = thread_rng().next_u64();
        let server_version = "0.0.0".to_string();
        let pox_consensus_byte: u8 = thread_rng().gen();
        let network_byte: u8 = thread_rng().gen_range(0..=1);
        let network_id = if network_byte == 1 {
            CHAIN_ID_TESTNET
        } else {
            CHAIN_ID_MAINNET
        };
        PeerInfo {
            burn_block_height,
            stacks_tip_consensus_hash: ConsensusHash([stacks_tip_consensus_byte; 20]),
            stacks_tip: BlockHeaderHash([stacks_tip_byte; 32]),
            stacks_tip_height,
            server_version,
            pox_consensus: ConsensusHash([pox_consensus_byte; 20]),
            network_id,
        }
    }
    fn random_mock_proposal() -> MockProposal {
        let peer_info = random_peer_data();
        MockProposal {
            peer_info,
            signature: MessageSignature::empty(),
        }
    }

    #[test]
    fn verify_sign_mock_proposal() {
        let private_key = StacksPrivateKey::random();
        let public_key = StacksPublicKey::from_private(&private_key);

        let bad_private_key = StacksPrivateKey::random();
        let bad_public_key = StacksPublicKey::from_private(&bad_private_key);

        let mut mock_proposal = random_mock_proposal();
        assert!(!mock_proposal
            .verify(&public_key)
            .expect("Failed to verify MockProposal"));

        mock_proposal
            .sign(&private_key)
            .expect("Failed to sign MockProposal");

        assert!(mock_proposal
            .verify(&public_key)
            .expect("Failed to verify MockProposal"));
        assert!(!mock_proposal
            .verify(&bad_public_key)
            .expect("Failed to verify MockProposal"));
    }

    #[test]
    fn serde_peer_data() {
        let peer_data = random_peer_data();
        let serialized_data = peer_data.serialize_to_vec();
        let deserialized_data = read_next::<PeerInfo, _>(&mut &serialized_data[..])
            .expect("Failed to deserialize PeerInfo");
        assert_eq!(peer_data, deserialized_data);
    }

    #[test]
    fn serde_mock_proposal() {
        let mut mock_signature = random_mock_proposal();
        mock_signature.sign(&StacksPrivateKey::random()).unwrap();
        let serialized_signature = mock_signature.serialize_to_vec();
        let deserialized_signature = read_next::<MockProposal, _>(&mut &serialized_signature[..])
            .expect("Failed to deserialize MockSignature");
        assert_eq!(mock_signature, deserialized_signature);
    }

    #[test]
    fn serde_mock_signature() {
        let mut mock_signature = MockSignature {
            signature: MessageSignature::empty(),
            mock_proposal: random_mock_proposal(),
            metadata: SignerMessageMetadata::default(),
        };
        mock_signature
            .sign(&StacksPrivateKey::random())
            .expect("Failed to sign MockSignature");
        let serialized_signature = mock_signature.serialize_to_vec();
        let deserialized_signature = read_next::<MockSignature, _>(&mut &serialized_signature[..])
            .expect("Failed to deserialize MockSignature");
        assert_eq!(mock_signature, deserialized_signature);
    }

    #[test]
    fn serde_mock_block() {
        let mock_proposal = random_mock_proposal();
        let mock_signature_1 =
            MockSignature::new(mock_proposal.clone(), &StacksPrivateKey::random());
        let mock_signature_2 =
            MockSignature::new(mock_proposal.clone(), &StacksPrivateKey::random());
        let mock_block = MockBlock {
            mock_proposal,
            mock_signatures: vec![mock_signature_1, mock_signature_2],
        };
        let serialized_data = mock_block.serialize_to_vec();
        let deserialized_data = read_next::<MockBlock, _>(&mut &serialized_data[..])
            .expect("Failed to deserialize MockSignData");
        assert_eq!(mock_block, deserialized_data);
    }

    #[test]
    fn test_backwards_compatibility() {
        let block_rejected_hex = "010100000050426c6f636b206973206e6f7420612074656e7572652d737461727420626c6f636b2c20616e642068617320616e20756e7265636f676e697a65642074656e75726520636f6e73656e7375732068617368000691f95f84b7045f7dce7757052caa986ef042cb58f7df5031a3b5b5d0e3dda63e80000000006fb349212e1a1af1a3c712878d5159b5ec14636adb6f70be00a6da4ad4f88a9934d8a9abb229620dd8e0f225d63401e36c64817fb29e6c05591dcbe95c512df3";
        let block_rejected_bytes = hex_bytes(block_rejected_hex).unwrap();
        let block_accepted_hex = "010011717149677c2ac97d15ae5954f7a716f10100b9cb81a2bf27551b2f2e54ef19001c694f8134c5c90f2f2bcd330e9f423204884f001b5df0050f36a2c4ff79dd93522bb2ae395ea87de4964886447507c18374b7a46ee2e371e9bf332f0706a3e8";
        let block_accepted_bytes = hex_bytes(block_accepted_hex).unwrap();
        let block_rejected = read_next::<SignerMessage, _>(&mut &block_rejected_bytes[..])
            .expect("Failed to deserialize BlockRejection");
        let block_accepted = read_next::<SignerMessage, _>(&mut &block_accepted_bytes[..])
            .expect("Failed to deserialize BlockRejection");

        assert_eq!(
            block_rejected,
            SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                reason_code: RejectCode::ValidationFailed(ValidateRejectCode::NoSuchTenure),
                reason: "Block is not a tenure-start block, and has an unrecognized tenure consensus hash".to_string(),
                signer_signature_hash: Sha512Trunc256Sum::from_hex("91f95f84b7045f7dce7757052caa986ef042cb58f7df5031a3b5b5d0e3dda63e").unwrap(),
                chain_id: CHAIN_ID_TESTNET,
                signature: MessageSignature::from_hex("006fb349212e1a1af1a3c712878d5159b5ec14636adb6f70be00a6da4ad4f88a9934d8a9abb229620dd8e0f225d63401e36c64817fb29e6c05591dcbe95c512df3").unwrap(),
                metadata: SignerMessageMetadata::empty(),
                response_data: BlockResponseData::new(u64::MAX, RejectReason::NotRejected),
            }))
        );

        assert_eq!(
            block_accepted,
            SignerMessage::BlockResponse(BlockResponse::Accepted(BlockAccepted {
                signer_signature_hash: Sha512Trunc256Sum::from_hex(
                    "11717149677c2ac97d15ae5954f7a716f10100b9cb81a2bf27551b2f2e54ef19"
                )
                .unwrap(),
                metadata: SignerMessageMetadata::empty(),
                signature: MessageSignature::from_hex("001c694f8134c5c90f2f2bcd330e9f423204884f001b5df0050f36a2c4ff79dd93522bb2ae395ea87de4964886447507c18374b7a46ee2e371e9bf332f0706a3e8").unwrap(),
                response_data: BlockResponseData::new(u64::MAX, RejectReason::NotRejected),
            }))
        );
    }

    #[test]
    fn test_block_response_metadata() {
        let block_rejected_hex = "010100000050426c6f636b206973206e6f7420612074656e7572652d737461727420626c6f636b2c20616e642068617320616e20756e7265636f676e697a65642074656e75726520636f6e73656e7375732068617368000691f95f84b7045f7dce7757052caa986ef042cb58f7df5031a3b5b5d0e3dda63e80000000006fb349212e1a1af1a3c712878d5159b5ec14636adb6f70be00a6da4ad4f88a9934d8a9abb229620dd8e0f225d63401e36c64817fb29e6c05591dcbe95c512df30000000b48656c6c6f20776f726c64";
        let block_rejected_bytes = hex_bytes(block_rejected_hex).unwrap();
        let block_accepted_hex = "010011717149677c2ac97d15ae5954f7a716f10100b9cb81a2bf27551b2f2e54ef19001c694f8134c5c90f2f2bcd330e9f423204884f001b5df0050f36a2c4ff79dd93522bb2ae395ea87de4964886447507c18374b7a46ee2e371e9bf332f0706a3e80000000b48656c6c6f20776f726c64";
        let block_accepted_bytes = hex_bytes(block_accepted_hex).unwrap();
        let block_rejected = read_next::<SignerMessage, _>(&mut &block_rejected_bytes[..])
            .expect("Failed to deserialize BlockRejection");
        let block_accepted = read_next::<SignerMessage, _>(&mut &block_accepted_bytes[..])
            .expect("Failed to deserialize BlockRejection");

        assert_eq!(
            block_rejected,
            SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                reason_code: RejectCode::ValidationFailed(ValidateRejectCode::NoSuchTenure),
                reason: "Block is not a tenure-start block, and has an unrecognized tenure consensus hash".to_string(),
                signer_signature_hash: Sha512Trunc256Sum::from_hex("91f95f84b7045f7dce7757052caa986ef042cb58f7df5031a3b5b5d0e3dda63e").unwrap(),
                chain_id: CHAIN_ID_TESTNET,
                signature: MessageSignature::from_hex("006fb349212e1a1af1a3c712878d5159b5ec14636adb6f70be00a6da4ad4f88a9934d8a9abb229620dd8e0f225d63401e36c64817fb29e6c05591dcbe95c512df3").unwrap(),
                metadata: SignerMessageMetadata {
                    server_version: "Hello world".to_string(),
                },
                response_data: BlockResponseData::new(u64::MAX, RejectReason::NotRejected),
            }))
        );

        assert_eq!(
            block_accepted,
            SignerMessage::BlockResponse(BlockResponse::Accepted(BlockAccepted {
                signer_signature_hash: Sha512Trunc256Sum::from_hex(
                    "11717149677c2ac97d15ae5954f7a716f10100b9cb81a2bf27551b2f2e54ef19"
                )
                .unwrap(),
                metadata: SignerMessageMetadata {
                    server_version: "Hello world".to_string(),
                },
                signature: MessageSignature::from_hex("001c694f8134c5c90f2f2bcd330e9f423204884f001b5df0050f36a2c4ff79dd93522bb2ae395ea87de4964886447507c18374b7a46ee2e371e9bf332f0706a3e8").unwrap(),
                response_data: BlockResponseData::empty(),
            }))
        );
    }

    #[test]
    fn test_empty_metadata() {
        let serialized_metadata = [0u8; 0];
        let deserialized_metadata =
            read_next::<SignerMessageMetadata, _>(&mut &serialized_metadata[..])
                .expect("Failed to deserialize SignerMessageMetadata");
        assert_eq!(deserialized_metadata, SignerMessageMetadata::empty());
    }

    #[test]
    fn block_response_data_serialization() {
        let mut response_data = BlockResponseData::new(2, RejectReason::ReorgNotAllowed);
        response_data.unknown_bytes = vec![1, 2, 3, 4];
        let mut bytes = vec![];
        response_data.consensus_serialize(&mut bytes).unwrap();
        // 1 byte version + 4 bytes (bytes_len) + 8 bytes tenure_extend_timestamp
        //   + 1 byte reject code + 4 bytes unknown_bytes
        assert_eq!(bytes.len(), 18);
        let deserialized_data = read_next::<BlockResponseData, _>(&mut &bytes[..])
            .expect("Failed to deserialize BlockResponseData");
        assert_eq!(response_data, deserialized_data);

        let response_data = BlockResponseData::new(2, RejectReason::NotRejected);
        let mut bytes = vec![];
        response_data.consensus_serialize(&mut bytes).unwrap();
        // 1 byte version + 4 bytes (bytes_len) + 8 bytes tenure_extend_timestamp + 0 bytes unknown_bytes
        assert_eq!(bytes.len(), 14);
        let deserialized_data = read_next::<BlockResponseData, _>(&mut &bytes[..])
            .expect("Failed to deserialize BlockResponseData");
        assert_eq!(response_data, deserialized_data);
    }

    /// Mock struct for testing "future proofing" of the block response data
    pub struct NewerBlockResponseData {
        pub version: u8,
        pub tenure_extend_timestamp: u64,
        pub reject_reason: RejectReason,
        pub some_other_field: u64,
        pub yet_another_field: u64,
    }

    impl NewerBlockResponseData {
        pub fn inner_consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
            write_next(fd, &self.tenure_extend_timestamp)?;
            write_next(fd, &self.reject_reason)?;
            write_next(fd, &self.some_other_field)?;
            write_next(fd, &self.yet_another_field)?;
            Ok(())
        }

        pub fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
            write_next(fd, &self.version)?;
            let mut inner_bytes = vec![];
            self.inner_consensus_serialize(&mut inner_bytes)?;
            let bytes_len = inner_bytes.len() as u32;
            write_next(fd, &bytes_len)?;
            fd.write_all(&inner_bytes).map_err(CodecError::WriteError)?;
            Ok(())
        }
    }

    #[test]
    fn test_newer_block_response_data() {
        let new_response_data = NewerBlockResponseData {
            version: 11,
            tenure_extend_timestamp: 2,
            reject_reason: RejectReason::ReorgNotAllowed,
            some_other_field: 3,
            yet_another_field: 4,
        };

        let mut bytes = vec![];
        new_response_data.consensus_serialize(&mut bytes).unwrap();
        let mut reader = bytes.as_slice();
        let deserialized_data = read_next::<BlockResponseData, _>(&mut reader)
            .expect("Failed to deserialize BlockResponseData");
        assert_eq!(reader.len(), 0, "Expected bytes to be fully consumed");
        assert_eq!(deserialized_data.version, 11);
        assert_eq!(deserialized_data.tenure_extend_timestamp, 2);
        assert_eq!(
            deserialized_data.reject_reason,
            RejectReason::ReorgNotAllowed
        );
        // two extra u64s:
        assert_eq!(deserialized_data.unknown_bytes.len(), 16);

        // BlockResponseData with unknown bytes can serialize/deserialize back to itself
        let mut bytes = vec![];
        deserialized_data.consensus_serialize(&mut bytes).unwrap();
        let deserialized_data_2 = read_next::<BlockResponseData, _>(&mut &bytes[..])
            .expect("Failed to deserialize BlockResponseData");
        assert_eq!(deserialized_data, deserialized_data_2);
    }

    /// Test using an older version of BlockAccepted to verify that we can deserialize
    /// future versions

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct BlockAcceptedOld {
        /// The signer signature hash of the block that was accepted
        pub signer_signature_hash: Sha512Trunc256Sum,
        /// The signer's signature across the acceptance
        pub signature: MessageSignature,
        /// Signer message metadata
        pub metadata: SignerMessageMetadata,
    }

    impl StacksMessageCodec for BlockAcceptedOld {
        fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
            write_next(fd, &self.signer_signature_hash)?;
            write_next(fd, &self.signature)?;
            write_next(fd, &self.metadata)?;
            Ok(())
        }

        fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<Self, CodecError> {
            let signer_signature_hash = read_next::<Sha512Trunc256Sum, _>(fd)?;
            let signature = read_next::<MessageSignature, _>(fd)?;
            let metadata = read_next::<SignerMessageMetadata, _>(fd)?;
            Ok(Self {
                signer_signature_hash,
                signature,
                metadata,
            })
        }
    }

    #[test]
    fn block_accepted_old_version_can_deserialize() {
        let block_accepted = BlockAccepted {
            signer_signature_hash: Sha512Trunc256Sum::from_hex("11717149677c2ac97d15ae5954f7a716f10100b9cb81a2bf27551b2f2e54ef19").unwrap(),
            metadata: SignerMessageMetadata::default(),
            signature: MessageSignature::from_hex("001c694f8134c5c90f2f2bcd330e9f423204884f001b5df0050f36a2c4ff79dd93522bb2ae395ea87de4964886447507c18374b7a46ee2e371e9bf332f0706a3e8").unwrap(),
            response_data: BlockResponseData::new(u64::MAX, RejectReason::NotRejected),
        };

        let mut bytes = vec![];
        block_accepted.consensus_serialize(&mut bytes).unwrap();

        // Ensure the old version can deserialize
        let block_accepted_old = read_next::<BlockAcceptedOld, _>(&mut &bytes[..])
            .expect("Failed to deserialize BlockAcceptedOld");
        assert_eq!(
            block_accepted.signer_signature_hash,
            block_accepted_old.signer_signature_hash
        );
        assert_eq!(block_accepted.signature, block_accepted_old.signature);
        assert_eq!(block_accepted.metadata, block_accepted_old.metadata);
    }
}
