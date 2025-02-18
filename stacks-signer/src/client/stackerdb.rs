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
//
use blockstack_lib::net::api::poststackerdbchunk::StackerDBErrorCodes;
use clarity::codec::read_next;
use hashbrown::HashMap;
use libsigner::{MessageSlotID, SignerMessage, SignerSession, StackerDBSession};
use libstackerdb::{StackerDBChunkAckData, StackerDBChunkData};
use slog::{slog_debug, slog_info, slog_warn};
use stacks_common::types::chainstate::StacksPrivateKey;
use stacks_common::util::hash::to_hex;
use stacks_common::{debug, info, warn};

use crate::client::{retry_with_exponential_backoff, ClientError};
use crate::config::{SignerConfig, SignerConfigMode};

/// The signer StackerDB slot ID, purposefully wrapped to prevent conflation with SignerID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, PartialOrd, Ord)]
pub struct SignerSlotID(pub u32);

impl std::fmt::Display for SignerSlotID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug)]
enum StackerDBMode {
    DryRun,
    Normal { signer_slot_id: SignerSlotID },
}

/// The StackerDB client for communicating with the .signers contract
#[derive(Debug)]
pub struct StackerDB<M: MessageSlotID + std::cmp::Eq> {
    /// The stacker-db sessions for each signer set and message type.
    /// Maps message ID to the DB session.
    signers_message_stackerdb_sessions: HashMap<M, StackerDBSession>,
    /// The private key used in all stacks node communications
    stacks_private_key: StacksPrivateKey,
    /// A map of a message ID to last chunk version for each session
    slot_versions: HashMap<M, HashMap<SignerSlotID, u32>>,
    /// The running mode of the stackerdb (whether the signer is running in dry-run or
    ///  normal operation)
    mode: StackerDBMode,
    /// The reward cycle of the connecting signer
    reward_cycle: u64,
}

impl<M: MessageSlotID + 'static> From<&SignerConfig> for StackerDB<M> {
    fn from(config: &SignerConfig) -> Self {
        let mode = match config.signer_mode {
            SignerConfigMode::DryRun => StackerDBMode::DryRun,
            SignerConfigMode::Normal {
                ref signer_slot_id, ..
            } => StackerDBMode::Normal {
                signer_slot_id: *signer_slot_id,
            },
        };

        Self::new(
            &config.node_host,
            config.stacks_private_key,
            config.mainnet,
            config.reward_cycle,
            mode,
        )
    }
}

impl<M: MessageSlotID + 'static> StackerDB<M> {
    #[cfg(any(test, feature = "testing"))]
    /// Create a StackerDB client in normal operation (i.e., not a dry-run signer)
    pub fn new_normal(
        host: &str,
        stacks_private_key: StacksPrivateKey,
        is_mainnet: bool,
        reward_cycle: u64,
        signer_slot_id: SignerSlotID,
    ) -> Self {
        Self::new(
            host,
            stacks_private_key,
            is_mainnet,
            reward_cycle,
            StackerDBMode::Normal { signer_slot_id },
        )
    }

    /// Create a new StackerDB client
    fn new(
        host: &str,
        stacks_private_key: StacksPrivateKey,
        is_mainnet: bool,
        reward_cycle: u64,
        signer_mode: StackerDBMode,
    ) -> Self {
        let mut signers_message_stackerdb_sessions = HashMap::new();
        for msg_id in M::all() {
            let session =
                StackerDBSession::new(host, msg_id.stacker_db_contract(is_mainnet, reward_cycle));
            signers_message_stackerdb_sessions.insert(*msg_id, session);
        }

        Self {
            signers_message_stackerdb_sessions,
            stacks_private_key,
            slot_versions: HashMap::new(),
            mode: signer_mode,
            reward_cycle,
        }
    }

    /// Sends messages to the .signers stacker-db with an exponential backoff retry
    pub fn send_message_with_retry<T: SignerMessage<M>>(
        &mut self,
        message: T,
    ) -> Result<StackerDBChunkAckData, ClientError> {
        let msg_id = message.msg_id().ok_or_else(|| {
            ClientError::PutChunkRejected(
                "Tried to send a SignerMessage which does not have a corresponding .signers slot identifier".into()
            )
        })?;
        let message_bytes = message.serialize_to_vec();
        self.send_message_bytes_with_retry(&msg_id, message_bytes)
    }

    /// Sends message (as a raw msg ID and bytes) to the .signers stacker-db with an
    /// exponential backoff retry
    pub fn send_message_bytes_with_retry(
        &mut self,
        msg_id: &M,
        message_bytes: Vec<u8>,
    ) -> Result<StackerDBChunkAckData, ClientError> {
        let StackerDBMode::Normal {
            signer_slot_id: slot_id,
        } = &self.mode
        else {
            info!(
                "Dry-run signer would have sent a stackerdb message";
                "message_id" => ?msg_id,
                "message_bytes" => to_hex(&message_bytes)
            );
            return Ok(StackerDBChunkAckData {
                accepted: true,
                reason: None,
                metadata: None,
                code: None,
            });
        };
        loop {
            let mut slot_version = if let Some(versions) = self.slot_versions.get_mut(msg_id) {
                if let Some(version) = versions.get(slot_id) {
                    *version
                } else {
                    versions.insert(*slot_id, 0);
                    1
                }
            } else {
                let mut versions = HashMap::new();
                versions.insert(*slot_id, 0);
                self.slot_versions.insert(*msg_id, versions);
                1
            };

            let mut chunk = StackerDBChunkData::new(slot_id.0, slot_version, message_bytes.clone());
            chunk.sign(&self.stacks_private_key)?;

            let Some(session) = self.signers_message_stackerdb_sessions.get_mut(msg_id) else {
                panic!("FATAL: would loop forever trying to send a message with ID {msg_id:?}, for which we don't have a session");
            };

            debug!(
                "Sending a chunk to stackerdb slot ID {slot_id} with version {slot_version} and message ID {msg_id:?} to contract {:?}!\n{chunk:?}",
                &session.stackerdb_contract_id
            );

            let send_request = || session.put_chunk(&chunk).map_err(backoff::Error::transient);
            let chunk_ack: StackerDBChunkAckData = retry_with_exponential_backoff(send_request)?;

            if let Some(versions) = self.slot_versions.get_mut(msg_id) {
                // NOTE: per the above, this is always executed
                versions.insert(*slot_id, slot_version.saturating_add(1));
            } else {
                return Err(ClientError::NotConnected);
            }

            if chunk_ack.accepted {
                debug!("Chunk accepted by stackerdb: {chunk_ack:?}");
                return Ok(chunk_ack);
            } else {
                warn!("Chunk rejected by stackerdb: {chunk_ack:?}");
            }
            if let Some(code) = chunk_ack.code {
                match StackerDBErrorCodes::from_code(code) {
                    Some(StackerDBErrorCodes::DataAlreadyExists) => {
                        if let Some(slot_metadata) = chunk_ack.metadata {
                            warn!("Failed to send message to stackerdb due to wrong version number. Attempted {}. Expected {}. Retrying...", slot_version, slot_metadata.slot_version);
                            slot_version = slot_metadata.slot_version;
                        } else {
                            warn!("Failed to send message to stackerdb due to wrong version number. Attempted {}. Expected unknown version number. Incrementing and retrying...", slot_version);
                        }
                        if let Some(versions) = self.slot_versions.get_mut(msg_id) {
                            // NOTE: per the above, this is always executed
                            versions.insert(*slot_id, slot_version.saturating_add(1));
                        } else {
                            return Err(ClientError::NotConnected);
                        }
                    }
                    _ => {
                        warn!("Failed to send message to stackerdb: {:?}", chunk_ack);
                        return Err(ClientError::PutChunkRejected(
                            chunk_ack
                                .reason
                                .unwrap_or_else(|| "No reason given".to_string()),
                        ));
                    }
                }
            }
        }
    }

    /// Get all signer messages from stackerdb for the given slot IDs
    pub fn get_messages<T: SignerMessage<M>>(
        session: &mut StackerDBSession,
        slot_ids: &[u32],
    ) -> Result<Vec<T>, ClientError> {
        let mut messages = vec![];
        let send_request = || {
            session
                .get_latest_chunks(slot_ids)
                .map_err(backoff::Error::transient)
        };
        let chunk_ack = retry_with_exponential_backoff(send_request)?;
        for (i, chunk) in chunk_ack.iter().enumerate() {
            let Some(data) = chunk else {
                continue;
            };
            let Ok(message) = read_next::<T, _>(&mut &data[..]) else {
                if !data.is_empty() {
                    warn!("Failed to deserialize chunk data into a SignerMessage");
                    debug!("slot #{i}: Failed chunk ({}): {data:?}", &data.len(),);
                }
                continue;
            };
            messages.push(message);
        }
        Ok(messages)
    }

    /// Retrieve the signer set this stackerdb client is attached to
    pub fn get_signer_set(&self) -> u32 {
        u32::try_from(self.reward_cycle % 2).expect("FATAL: reward cycle % 2 exceeds u32::MAX")
    }

    /// Get the session corresponding to the given message ID if it exists
    pub fn get_session_mut(&mut self, msg_id: &M) -> Option<&mut StackerDBSession> {
        self.signers_message_stackerdb_sessions.get_mut(msg_id)
    }
}

#[cfg(test)]
mod tests {
    use std::thread::spawn;
    use std::time::Duration;

    use blockstack_lib::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader};
    use clarity::util::hash::{MerkleTree, Sha512Trunc256Sum};
    use clarity::util::secp256k1::MessageSignature;
    use libsigner::v0::messages::{
        BlockRejection, BlockResponse, BlockResponseData, RejectCode, RejectReason, SignerMessage,
        SignerMessageMetadata,
    };
    use rand::{thread_rng, RngCore};

    use super::*;
    use crate::client::tests::{generate_signer_config, mock_server_from_config, write_response};
    use crate::config::{build_signer_config_tomls, GlobalConfig, Network};

    #[test]
    fn send_signer_message_should_succeed() {
        let signer_config = build_signer_config_tomls(
            &[StacksPrivateKey::random()],
            "localhost:20443",
            Some(Duration::from_millis(128)), // Timeout defaults to 5 seconds. Let's override it to 128 milliseconds.
            &Network::Testnet,
            "1234",
            16,
            3000,
            Some(100_000),
            None,
            Some(9000),
            None,
        );
        let config = GlobalConfig::load_from_str(&signer_config[0]).unwrap();
        let signer_config = generate_signer_config(&config, 5);
        let mut stackerdb = StackerDB::from(&signer_config);

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

        let block_reject = BlockRejection {
            reason: "Did not like it".into(),
            reason_code: RejectCode::RejectedInPriorRound,
            signer_signature_hash: block.header.signer_signature_hash(),
            chain_id: thread_rng().next_u32(),
            signature: MessageSignature::empty(),
            metadata: SignerMessageMetadata::empty(),
            response_data: BlockResponseData::new(
                thread_rng().next_u64(),
                RejectReason::RejectedInPriorRound,
            ),
        };
        let signer_message = SignerMessage::BlockResponse(BlockResponse::Rejected(block_reject));
        let ack = StackerDBChunkAckData {
            accepted: true,
            reason: None,
            metadata: None,
            code: None,
        };
        let mock_server = mock_server_from_config(&config);
        debug!("Spawning msg sender");
        let sender_thread =
            spawn(move || stackerdb.send_message_with_retry(signer_message).unwrap());
        let mut response_bytes = b"HTTP/1.1 200 OK\n\n".to_vec();
        let payload = serde_json::to_string(&ack).expect("Failed to serialize ack");
        response_bytes.extend(payload.as_bytes());
        std::thread::sleep(Duration::from_millis(500));
        write_response(mock_server, response_bytes.as_slice());
        assert_eq!(ack, sender_thread.join().unwrap());
    }
}
