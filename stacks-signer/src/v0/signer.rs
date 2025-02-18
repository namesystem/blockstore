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
use std::collections::HashMap;
use std::fmt::Debug;
use std::sync::mpsc::Sender;
use std::time::{Duration, Instant};

use blockstack_lib::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader};
use blockstack_lib::net::api::postblock_proposal::{
    BlockValidateOk, BlockValidateReject, BlockValidateResponse, TOO_MANY_REQUESTS_STATUS,
};
use blockstack_lib::util_lib::db::Error as DBError;
use clarity::types::chainstate::StacksPrivateKey;
use clarity::types::{PrivateKey, StacksEpochId};
use clarity::util::hash::{MerkleHashFunc, Sha512Trunc256Sum};
use clarity::util::secp256k1::Secp256k1PublicKey;
use libsigner::v0::messages::{
    BlockAccepted, BlockRejection, BlockResponse, MessageSlotID, MockProposal, MockSignature,
    RejectReason, SignerMessage,
};
use libsigner::{BlockProposal, SignerEvent};
use slog::{slog_debug, slog_error, slog_info, slog_warn};
use stacks_common::types::chainstate::StacksAddress;
use stacks_common::util::get_epoch_time_secs;
use stacks_common::util::secp256k1::MessageSignature;
use stacks_common::{debug, error, info, warn};

use crate::chainstate::{ProposalEvalConfig, SortitionsView};
use crate::client::{ClientError, SignerSlotID, StackerDB, StacksClient};
use crate::config::{SignerConfig, SignerConfigMode};
use crate::runloop::SignerResult;
use crate::signerdb::{BlockInfo, BlockState, SignerDb};
use crate::Signer as SignerTrait;

/// Signer running mode (whether dry-run or real)
#[derive(Debug)]
pub enum SignerMode {
    /// Dry run operation: signer is not actually registered, the signer
    ///  will not submit stackerdb messages, etc.
    DryRun,
    /// Normal signer operation: if registered, the signer will submit
    /// stackerdb messages, etc.
    Normal {
        /// The signer ID assigned to this signer (may be different from signer_slot_id)
        signer_id: u32,
    },
}

/// The stacks signer registered for the reward cycle
#[derive(Debug)]
pub struct Signer {
    /// The private key of the signer
    #[cfg(any(test, feature = "testing"))]
    pub private_key: StacksPrivateKey,
    #[cfg(not(any(test, feature = "testing")))]
    /// The private key of the signer
    private_key: StacksPrivateKey,
    /// The stackerdb client
    pub stackerdb: StackerDB<MessageSlotID>,
    /// Whether the signer is a mainnet signer or not
    pub mainnet: bool,
    /// The running mode of the signer (whether dry-run or normal)
    pub mode: SignerMode,
    /// The signer slot ids for the signers in the reward cycle
    pub signer_slot_ids: Vec<SignerSlotID>,
    /// The addresses of other signers
    pub signer_addresses: Vec<StacksAddress>,
    /// The reward cycle this signer belongs to
    pub reward_cycle: u64,
    /// Reward set signer addresses and their weights
    pub signer_weights: HashMap<StacksAddress, u32>,
    /// SignerDB for state management
    pub signer_db: SignerDb,
    /// Configuration for proposal evaluation
    pub proposal_config: ProposalEvalConfig,
    /// How long to wait for a block proposal validation response to arrive before
    /// marking a submitted block as invalid
    pub block_proposal_validation_timeout: Duration,
    /// The current submitted block proposal and its submission time
    pub submitted_block_proposal: Option<(Sha512Trunc256Sum, Instant)>,
    /// Maximum age of a block proposal in seconds before it is dropped without processing
    pub block_proposal_max_age_secs: u64,
}

impl std::fmt::Display for SignerMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SignerMode::DryRun => write!(f, "Dry-Run signer"),
            SignerMode::Normal { signer_id } => write!(f, "Signer #{signer_id}"),
        }
    }
}

impl std::fmt::Display for Signer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cycle #{} {}", self.reward_cycle, self.mode)
    }
}

impl SignerTrait<SignerMessage> for Signer {
    /// Create a new signer from the given configuration
    fn new(config: SignerConfig) -> Self {
        Self::from(config)
    }

    /// Return the reward cycle of the signer
    fn reward_cycle(&self) -> u64 {
        self.reward_cycle
    }

    /// Process the event
    fn process_event(
        &mut self,
        stacks_client: &StacksClient,
        sortition_state: &mut Option<SortitionsView>,
        event: Option<&SignerEvent<SignerMessage>>,
        _res: &Sender<Vec<SignerResult>>,
        current_reward_cycle: u64,
    ) {
        let event_parity = match event {
            // Block proposal events do have reward cycles, but each proposal has its own cycle,
            //  and the vec could be heterogeneous, so, don't differentiate.
            Some(SignerEvent::BlockValidationResponse(_))
            | Some(SignerEvent::MinerMessages(..))
            | Some(SignerEvent::NewBurnBlock { .. })
            | Some(SignerEvent::NewBlock { .. })
            | Some(SignerEvent::StatusCheck)
            | None => None,
            Some(SignerEvent::SignerMessages(msg_parity, ..)) => Some(u64::from(*msg_parity) % 2),
        };
        let other_signer_parity = (self.reward_cycle + 1) % 2;
        if event_parity == Some(other_signer_parity) {
            return;
        }
        self.check_submitted_block_proposal();
        debug!("{self}: Processing event: {event:?}");
        let Some(event) = event else {
            // No event. Do nothing.
            debug!("{self}: No event received");
            return;
        };
        if self.reward_cycle > current_reward_cycle
            && !matches!(
                event,
                SignerEvent::StatusCheck | SignerEvent::NewBurnBlock { .. }
            )
        {
            // The reward cycle has not yet started for this signer instance
            // Do not process any events other than status checks or new burn blocks
            debug!("{self}: Signer reward cycle has not yet started. Ignoring event.");
            return;
        }
        match event {
            SignerEvent::BlockValidationResponse(block_validate_response) => {
                debug!("{self}: Received a block proposal result from the stacks node...");
                self.handle_block_validate_response(stacks_client, block_validate_response)
            }
            SignerEvent::SignerMessages(_signer_set, messages) => {
                debug!(
                    "{self}: Received {} messages from the other signers",
                    messages.len()
                );
                // try and gather signatures
                for message in messages {
                    let SignerMessage::BlockResponse(block_response) = message else {
                        continue;
                    };
                    self.handle_block_response(stacks_client, block_response);
                }
            }
            SignerEvent::MinerMessages(messages, miner_pubkey) => {
                debug!(
                    "{self}: Received {} messages from the miner",
                    messages.len();
                );
                for message in messages {
                    match message {
                        SignerMessage::BlockProposal(block_proposal) => {
                            #[cfg(any(test, feature = "testing"))]
                            if self.test_ignore_all_block_proposals(block_proposal) {
                                continue;
                            }
                            self.handle_block_proposal(
                                stacks_client,
                                sortition_state,
                                block_proposal,
                                miner_pubkey,
                            );
                        }
                        SignerMessage::BlockPushed(b) => {
                            // This will infinitely loop until the block is acknowledged by the node
                            info!(
                                "{self}: Got block pushed message";
                                "block_id" => %b.block_id(),
                                "block_height" => b.header.chain_length,
                                "signer_sighash" => %b.header.signer_signature_hash(),
                            );
                            #[cfg(any(test, feature = "testing"))]
                            if self.test_skip_block_broadcast(b) {
                                return;
                            }
                            stacks_client.post_block_until_ok(self, b);
                        }
                        SignerMessage::MockProposal(mock_proposal) => {
                            let epoch = match stacks_client.get_node_epoch() {
                                Ok(epoch) => epoch,
                                Err(e) => {
                                    warn!("{self}: Failed to determine node epoch. Cannot mock sign: {e}");
                                    return;
                                }
                            };
                            info!("{self}: received a mock block proposal.";
                                "current_reward_cycle" => current_reward_cycle,
                                "epoch" => ?epoch
                            );
                            if epoch == StacksEpochId::Epoch25
                                && self.reward_cycle == current_reward_cycle
                            {
                                // We are in epoch 2.5, so we should mock sign to prove we are still alive.
                                self.mock_sign(mock_proposal.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
            SignerEvent::StatusCheck => {
                debug!("{self}: Received a status check event.");
            }
            SignerEvent::NewBurnBlock {
                burn_height,
                burn_header_hash,
                received_time,
            } => {
                info!("{self}: Received a new burn block event for block height {burn_height}");
                self.signer_db
                    .insert_burn_block(burn_header_hash, *burn_height, received_time)
                    .unwrap_or_else(|e| {
                        error!(
                            "Failed to write burn block event to signerdb";
                            "err" => ?e,
                            "burn_header_hash" => %burn_header_hash,
                            "burn_height" => burn_height
                        );
                        panic!("{self} Failed to write burn block event to signerdb: {e}");
                    });
                *sortition_state = None;
            }
            SignerEvent::NewBlock {
                block_hash,
                block_height,
            } => {
                debug!(
                    "{self}: Received a new block event.";
                    "block_hash" => %block_hash,
                    "block_height" => block_height
                );
                if let Ok(Some(mut block_info)) = self
                    .signer_db
                    .block_lookup(block_hash)
                    .inspect_err(|e| warn!("{self}: Failed to load block state: {e:?}"))
                {
                    if block_info.state == BlockState::GloballyAccepted {
                        // We have already globally accepted this block. Do nothing.
                        return;
                    }
                    if let Err(e) = self.signer_db.mark_block_globally_accepted(&mut block_info) {
                        warn!("{self}: Failed to mark block as globally accepted: {e:?}");
                        return;
                    }
                    if let Err(e) = self.signer_db.insert_block(&block_info) {
                        warn!("{self}: Failed to update block state to globally accepted: {e:?}");
                    }
                }
            }
        }
    }

    fn has_unprocessed_blocks(&self) -> bool {
        self.signer_db
            .has_unprocessed_blocks(self.reward_cycle)
            .unwrap_or_else(|e| {
                error!("{self}: Failed to check for pending blocks: {e:?}",);
                // Assume we have pending blocks to prevent premature cleanup
                true
            })
    }
}

impl From<SignerConfig> for Signer {
    fn from(signer_config: SignerConfig) -> Self {
        let stackerdb = StackerDB::from(&signer_config);
        let mode = match signer_config.signer_mode {
            SignerConfigMode::DryRun => SignerMode::DryRun,
            SignerConfigMode::Normal { signer_id, .. } => SignerMode::Normal { signer_id },
        };

        debug!("Reward cycle #{} {mode}", signer_config.reward_cycle);

        let signer_db =
            SignerDb::new(&signer_config.db_path).expect("Failed to connect to signer Db");
        let proposal_config = ProposalEvalConfig::from(&signer_config);

        Self {
            private_key: signer_config.stacks_private_key,
            stackerdb,
            mainnet: signer_config.mainnet,
            mode,
            signer_addresses: signer_config.signer_entries.signer_addresses.clone(),
            signer_weights: signer_config.signer_entries.signer_addr_to_weight.clone(),
            signer_slot_ids: signer_config.signer_slot_ids.clone(),
            reward_cycle: signer_config.reward_cycle,
            signer_db,
            proposal_config,
            submitted_block_proposal: None,
            block_proposal_validation_timeout: signer_config.block_proposal_validation_timeout,
            block_proposal_max_age_secs: signer_config.block_proposal_max_age_secs,
        }
    }
}

impl Signer {
    /// Determine this signers response to a proposed block
    /// Returns a BlockResponse if we have already validated the block
    /// Returns None otherwise
    fn determine_response(&mut self, block_info: &BlockInfo) -> Option<BlockResponse> {
        let valid = block_info.valid?;
        let response = if valid {
            debug!("{self}: Accepting block {}", block_info.block.block_id());
            self.create_block_acceptance(&block_info.block)
        } else {
            debug!("{self}: Rejecting block {}", block_info.block.block_id());
            self.create_block_rejection(RejectReason::RejectedInPriorRound, &block_info.block)
        };
        Some(response)
    }

    /// Create a block acceptance response for a block
    pub fn create_block_acceptance(&self, block: &NakamotoBlock) -> BlockResponse {
        let signature = self
            .private_key
            .sign(block.header.signer_signature_hash().bits())
            .expect("Failed to sign block");
        BlockResponse::accepted(
            block.header.signer_signature_hash(),
            signature,
            self.signer_db.calculate_tenure_extend_timestamp(
                self.proposal_config
                    .tenure_idle_timeout
                    .saturating_add(self.proposal_config.tenure_idle_timeout_buffer),
                block,
                true,
            ),
        )
    }
    /// Create a block rejection response for a block with the given reject code
    pub fn create_block_rejection(
        &self,
        reject_reason: RejectReason,
        block: &NakamotoBlock,
    ) -> BlockResponse {
        BlockResponse::rejected(
            block.header.signer_signature_hash(),
            reject_reason,
            &self.private_key,
            self.mainnet,
            self.signer_db.calculate_tenure_extend_timestamp(
                self.proposal_config
                    .tenure_idle_timeout
                    .saturating_add(self.proposal_config.tenure_idle_timeout_buffer),
                block,
                false,
            ),
        )
    }
    /// Check if block should be rejected based on sortition state
    /// Will return a BlockResponse::Rejection if the block is invalid, none otherwise.
    fn check_block_against_sortition_state(
        &mut self,
        stacks_client: &StacksClient,
        sortition_state: &mut Option<SortitionsView>,
        block: &NakamotoBlock,
        miner_pubkey: &Secp256k1PublicKey,
    ) -> Option<BlockResponse> {
        let signer_signature_hash = block.header.signer_signature_hash();
        let block_id = block.block_id();
        // Get sortition view if we don't have it
        if sortition_state.is_none() {
            *sortition_state =
                SortitionsView::fetch_view(self.proposal_config.clone(), stacks_client)
                    .inspect_err(|e| {
                        warn!(
                            "{self}: Failed to update sortition view: {e:?}";
                            "signer_sighash" => %signer_signature_hash,
                            "block_id" => %block_id,
                        )
                    })
                    .ok();
        }

        // Check if proposal can be rejected now if not valid against sortition view
        if let Some(sortition_state) = sortition_state {
            match sortition_state.check_proposal(
                stacks_client,
                &mut self.signer_db,
                block,
                miner_pubkey,
                true,
            ) {
                // Error validating block
                Err(RejectReason::ConnectivityIssues(e)) => {
                    warn!(
                        "{self}: Error checking block proposal: {e}";
                        "signer_sighash" => %signer_signature_hash,
                        "block_id" => %block_id,
                    );
                    Some(self.create_block_rejection(RejectReason::ConnectivityIssues(e), block))
                }
                // Block proposal is bad
                Err(reject_code) => {
                    warn!(
                        "{self}: Block proposal invalid";
                        "signer_sighash" => %signer_signature_hash,
                        "block_id" => %block_id,
                        "reject_reason" => %reject_code,
                        "reject_code" => ?reject_code,
                    );
                    Some(self.create_block_rejection(reject_code, block))
                }
                // Block proposal passed check, still don't know if valid
                Ok(_) => None,
            }
        } else {
            warn!(
                "{self}: Cannot validate block, no sortition view";
                "signer_sighash" => %signer_signature_hash,
                "block_id" => %block_id,
            );
            Some(self.create_block_rejection(RejectReason::NoSortitionView, block))
        }
    }

    /// Handle block proposal messages submitted to signers stackerdb
    fn handle_block_proposal(
        &mut self,
        stacks_client: &StacksClient,
        sortition_state: &mut Option<SortitionsView>,
        block_proposal: &BlockProposal,
        miner_pubkey: &Secp256k1PublicKey,
    ) {
        debug!("{self}: Received a block proposal: {block_proposal:?}");
        if block_proposal.reward_cycle != self.reward_cycle {
            // We are not signing for this reward cycle. Ignore the block.
            debug!(
                "{self}: Received a block proposal for a different reward cycle. Ignore it.";
                "requested_reward_cycle" => block_proposal.reward_cycle
            );
            return;
        }

        if block_proposal
            .block
            .header
            .timestamp
            .saturating_add(self.block_proposal_max_age_secs)
            < get_epoch_time_secs()
        {
            // Block is too old. Drop it with a warning. Don't even bother broadcasting to the node.
            warn!("{self}: Received a block proposal that is more than {} secs old. Ignoring...", self.block_proposal_max_age_secs;
                "signer_sighash" => %block_proposal.block.header.signer_signature_hash(),
                "block_id" => %block_proposal.block.block_id(),
                "block_height" => block_proposal.block.header.chain_length,
                "burn_height" => block_proposal.burn_height,
                "timestamp" => block_proposal.block.header.timestamp,
            );
            return;
        }

        // TODO: should add a check to ignore an old burn block height if we know its outdated. Would require us to store the burn block height we last saw on the side.
        //  the signer needs to be able to determine whether or not the block they're about to sign would conflict with an already-signed Stacks block
        let signer_signature_hash = block_proposal.block.header.signer_signature_hash();
        if let Some(block_info) = self.block_lookup_by_reward_cycle(&signer_signature_hash) {
            let Some(block_response) = self.determine_response(&block_info) else {
                // We are still waiting for a response for this block. Do nothing.
                debug!("{self}: Received a block proposal for a block we are already validating.";
                    "signer_sighash" => %signer_signature_hash,
                    "block_id" => %block_proposal.block.block_id()
                );
                return;
            };
            // Submit a proposal response to the .signers contract for miners
            debug!("{self}: Broadcasting a block response to stacks node: {block_response:?}");
            let accepted = matches!(block_response, BlockResponse::Accepted(..));
            match self
                .stackerdb
                .send_message_with_retry::<SignerMessage>(block_response.into())
            {
                Ok(_) => {
                    crate::monitoring::actions::increment_block_responses_sent(accepted);
                    crate::monitoring::actions::record_block_response_latency(
                        &block_proposal.block,
                    );
                }
                Err(e) => {
                    warn!("{self}: Failed to send block response to stacker-db: {e:?}",);
                }
            }
            return;
        }

        info!(
            "{self}: received a block proposal for a new block.";
            "signer_sighash" => %signer_signature_hash,
            "block_id" => %block_proposal.block.block_id(),
            "block_height" => block_proposal.block.header.chain_length,
            "burn_height" => block_proposal.burn_height,
            "consensus_hash" => %block_proposal.block.header.consensus_hash,
        );
        crate::monitoring::actions::increment_block_proposals_received();
        #[cfg(any(test, feature = "testing"))]
        let mut block_info = BlockInfo::from(block_proposal.clone());
        #[cfg(not(any(test, feature = "testing")))]
        let block_info = BlockInfo::from(block_proposal.clone());

        // Get sortition view if we don't have it
        if sortition_state.is_none() {
            *sortition_state =
                SortitionsView::fetch_view(self.proposal_config.clone(), stacks_client)
                    .inspect_err(|e| {
                        warn!(
                            "{self}: Failed to update sortition view: {e:?}";
                            "signer_sighash" => %signer_signature_hash,
                            "block_id" => %block_proposal.block.block_id(),
                        )
                    })
                    .ok();
        }

        // Check if proposal can be rejected now if not valid against sortition view
        let block_response = self.check_block_against_sortition_state(
            stacks_client,
            sortition_state,
            &block_proposal.block,
            miner_pubkey,
        );

        #[cfg(any(test, feature = "testing"))]
        let block_response =
            self.test_reject_block_proposal(block_proposal, &mut block_info, block_response);

        if let Some(block_response) = block_response {
            // We know proposal is invalid. Send rejection message, do not do further validation and do not store it.
            debug!("{self}: Broadcasting a block response to stacks node: {block_response:?}");
            let res = self
                .stackerdb
                .send_message_with_retry::<SignerMessage>(block_response.into());

            match res {
                Err(e) => warn!("{self}: Failed to send block rejection to stacker-db: {e:?}"),
                Ok(ack) if !ack.accepted => warn!(
                    "{self}: Block rejection not accepted by stacker-db: {:?}",
                    ack.reason
                ),
                Ok(_) => debug!("{self}: Block rejection accepted by stacker-db"),
            }
        } else {
            // Just in case check if the last block validation submission timed out.
            self.check_submitted_block_proposal();
            if self.submitted_block_proposal.is_none() {
                // We don't know if proposal is valid, submit to stacks-node for further checks and store it locally.
                info!(
                    "{self}: submitting block proposal for validation";
                    "signer_sighash" => %signer_signature_hash,
                    "block_id" => %block_proposal.block.block_id(),
                    "block_height" => block_proposal.block.header.chain_length,
                    "burn_height" => block_proposal.burn_height,
                );

                #[cfg(any(test, feature = "testing"))]
                self.test_stall_block_validation_submission();
                self.submit_block_for_validation(stacks_client, &block_proposal.block);
            } else {
                // Still store the block but log we can't submit it for validation. We may receive enough signatures/rejections
                // from other signers to push the proposed block into a global rejection/acceptance regardless of our participation.
                // However, we will not be able to participate beyond this until our block submission times out or we receive a response
                // from our node.
                warn!("{self}: cannot submit block proposal for validation as we are already waiting for a response for a prior submission. Inserting pending proposal.";
                    "signer_signature_hash" => signer_signature_hash.to_string(),
                );
                self.signer_db
                    .insert_pending_block_validation(&signer_signature_hash, get_epoch_time_secs())
                    .unwrap_or_else(|e| {
                        warn!("{self}: Failed to insert pending block validation: {e:?}")
                    });
            }

            // Do not store KNOWN invalid blocks as this could DOS the signer. We only store blocks that are valid or unknown.
            self.signer_db
                .insert_block(&block_info)
                .unwrap_or_else(|e| self.handle_insert_block_error(e));
        }
    }

    /// Handle block response messages from a signer
    fn handle_block_response(
        &mut self,
        stacks_client: &StacksClient,
        block_response: &BlockResponse,
    ) {
        match block_response {
            BlockResponse::Accepted(accepted) => {
                self.handle_block_signature(stacks_client, accepted);
            }
            BlockResponse::Rejected(block_rejection) => {
                self.handle_block_rejection(block_rejection);
            }
        };
    }

    /// WARNING: This is an incomplete check. Do NOT call this function PRIOR to check_proposal or block_proposal validation succeeds.
    ///
    /// Re-verify a block's chain length against the last signed block within signerdb.
    /// This is required in case a block has been approved since the initial checks of the block validation endpoint.
    fn check_block_against_signer_db_state(
        &mut self,
        stacks_client: &StacksClient,
        proposed_block: &NakamotoBlock,
    ) -> Option<BlockResponse> {
        let signer_signature_hash = proposed_block.header.signer_signature_hash();
        let proposed_block_consensus_hash = proposed_block.header.consensus_hash;
        // If this is a tenure change block, ensure that it confirms the correct number of blocks from the parent tenure.
        if let Some(tenure_change) = proposed_block.get_tenure_change_tx_payload() {
            // Ensure that the tenure change block confirms the expected parent block
            match SortitionsView::check_tenure_change_confirms_parent(
                tenure_change,
                proposed_block,
                &mut self.signer_db,
                stacks_client,
                self.proposal_config.tenure_last_block_proposal_timeout,
                self.proposal_config.reorg_attempts_activity_timeout,
            ) {
                Ok(true) => {}
                Ok(false) => {
                    return Some(self.create_block_rejection(
                        RejectReason::SortitionViewMismatch,
                        proposed_block,
                    ))
                }
                Err(e) => {
                    warn!("{self}: Error checking block proposal: {e}";
                        "signer_sighash" => %signer_signature_hash,
                        "block_id" => %proposed_block.block_id()
                    );
                    return Some(self.create_block_rejection(
                        RejectReason::ConnectivityIssues(
                            "error checking block proposal".to_string(),
                        ),
                        proposed_block,
                    ));
                }
            }
        }

        // Ensure that the block is the last block in the chain of its current tenure.
        match self
            .signer_db
            .get_last_accepted_block(&proposed_block_consensus_hash)
        {
            Ok(Some(last_block_info)) => {
                if proposed_block.header.chain_length <= last_block_info.block.header.chain_length {
                    warn!(
                        "Miner's block proposal does not confirm as many blocks as we expect";
                        "proposed_block_consensus_hash" => %proposed_block_consensus_hash,
                        "proposed_block_signer_sighash" => %signer_signature_hash,
                        "proposed_chain_length" => proposed_block.header.chain_length,
                        "expected_at_least" => last_block_info.block.header.chain_length + 1,
                    );
                    return Some(self.create_block_rejection(
                        RejectReason::SortitionViewMismatch,
                        proposed_block,
                    ));
                }
            }
            Ok(_) => {}
            Err(e) => {
                warn!("{self}: Failed to check block against signer db: {e}";
                    "signer_sighash" => %signer_signature_hash,
                    "block_id" => %proposed_block.block_id()
                );
                return Some(self.create_block_rejection(
                    RejectReason::ConnectivityIssues(
                        "failed to check block against signer db".to_string(),
                    ),
                    proposed_block,
                ));
            }
        }
        None
    }

    /// Handle the block validate ok response. Returns our block response if we have one
    fn handle_block_validate_ok(
        &mut self,
        stacks_client: &StacksClient,
        block_validate_ok: &BlockValidateOk,
    ) -> Option<BlockResponse> {
        crate::monitoring::actions::increment_block_validation_responses(true);
        let signer_signature_hash = block_validate_ok.signer_signature_hash;
        if self
            .submitted_block_proposal
            .map(|(proposal_hash, _)| proposal_hash == signer_signature_hash)
            .unwrap_or(false)
        {
            self.submitted_block_proposal = None;
        }
        // For mutability reasons, we need to take the block_info out of the map and add it back after processing
        let Some(mut block_info) = self.block_lookup_by_reward_cycle(&signer_signature_hash) else {
            // We have not seen this block before. Why are we getting a response for it?
            debug!("{self}: Received a block validate response for a block we have not seen before. Ignoring...");
            return None;
        };
        if block_info.is_locally_finalized() {
            debug!("{self}: Received block validation for a block that is already marked as {}. Ignoring...", block_info.state);
            return None;
        }

        if let Some(block_response) =
            self.check_block_against_signer_db_state(stacks_client, &block_info.block)
        {
            // The signer db state has changed. We no longer view this block as valid. Override the validation response.
            if let Err(e) = block_info.mark_locally_rejected() {
                if !block_info.has_reached_consensus() {
                    warn!("{self}: Failed to mark block as locally rejected: {e:?}");
                }
            };
            debug!("{self}: Broadcasting a block response to stacks node: {block_response:?}");
            let res = self
                .stackerdb
                .send_message_with_retry::<SignerMessage>(block_response.into());

            crate::monitoring::actions::record_block_response_latency(&block_info.block);

            match res {
                Err(e) => warn!("{self}: Failed to send block rejection to stacker-db: {e:?}"),
                Ok(ack) if !ack.accepted => warn!(
                    "{self}: Block rejection not accepted by stacker-db: {:?}",
                    ack.reason
                ),
                Ok(_) => debug!("{self}: Block rejection accepted by stacker-db"),
            }
            self.signer_db
                .insert_block(&block_info)
                .unwrap_or_else(|e| self.handle_insert_block_error(e));
            None
        } else {
            if let Err(e) = block_info.mark_locally_accepted(false) {
                if !block_info.has_reached_consensus() {
                    warn!("{self}: Failed to mark block as locally accepted: {e:?}",);
                    return None;
                }
                block_info.signed_self.get_or_insert(get_epoch_time_secs());
            }
            // Record the block validation time but do not consider stx transfers or boot contract calls
            block_info.validation_time_ms = if block_validate_ok.cost.is_zero() {
                Some(0)
            } else {
                Some(block_validate_ok.validation_time_ms)
            };

            self.signer_db
                .insert_block(&block_info)
                .unwrap_or_else(|e| self.handle_insert_block_error(e));
            let block_response = self.create_block_acceptance(&block_info.block);
            // have to save the signature _after_ the block info
            self.handle_block_signature(stacks_client, block_response.as_block_accepted()?);
            Some(block_response)
        }
    }

    /// Handle the block validate reject response. Returns our block response if we have one
    fn handle_block_validate_reject(
        &mut self,
        block_validate_reject: &BlockValidateReject,
    ) -> Option<BlockResponse> {
        crate::monitoring::actions::increment_block_validation_responses(false);
        let signer_signature_hash = block_validate_reject.signer_signature_hash;
        if self
            .submitted_block_proposal
            .map(|(proposal_hash, _)| proposal_hash == signer_signature_hash)
            .unwrap_or(false)
        {
            self.submitted_block_proposal = None;
        }
        let Some(mut block_info) = self.block_lookup_by_reward_cycle(&signer_signature_hash) else {
            // We have not seen this block before. Why are we getting a response for it?
            debug!("{self}: Received a block validate response for a block we have not seen before. Ignoring...");
            return None;
        };
        if block_info.is_locally_finalized() {
            debug!("{self}: Received block validation for a block that is already marked as {}. Ignoring...", block_info.state);
            return None;
        }
        if let Err(e) = block_info.mark_locally_rejected() {
            if !block_info.has_reached_consensus() {
                warn!("{self}: Failed to mark block as locally rejected: {e:?}",);
                return None;
            }
        }
        let block_rejection = BlockRejection::from_validate_rejection(
            block_validate_reject.clone(),
            &self.private_key,
            self.mainnet,
            self.signer_db.calculate_tenure_extend_timestamp(
                self.proposal_config
                    .tenure_idle_timeout
                    .saturating_add(self.proposal_config.tenure_idle_timeout_buffer),
                &block_info.block,
                false,
            ),
        );
        self.signer_db
            .insert_block(&block_info)
            .unwrap_or_else(|e| self.handle_insert_block_error(e));
        self.handle_block_rejection(&block_rejection);
        Some(BlockResponse::Rejected(block_rejection))
    }

    /// Handle the block validate response returned from our prior calls to submit a block for validation
    fn handle_block_validate_response(
        &mut self,
        stacks_client: &StacksClient,
        block_validate_response: &BlockValidateResponse,
    ) {
        info!("{self}: Received a block validate response: {block_validate_response:?}");
        let block_response = match block_validate_response {
            BlockValidateResponse::Ok(block_validate_ok) => {
                crate::monitoring::actions::record_block_validation_latency(
                    block_validate_ok.validation_time_ms,
                );
                self.handle_block_validate_ok(stacks_client, block_validate_ok)
            }
            BlockValidateResponse::Reject(block_validate_reject) => {
                self.handle_block_validate_reject(block_validate_reject)
            }
        };
        // Remove this block validation from the pending table
        let signer_sig_hash = block_validate_response.signer_signature_hash();
        self.signer_db
            .remove_pending_block_validation(&signer_sig_hash)
            .unwrap_or_else(|e| warn!("{self}: Failed to remove pending block validation: {e:?}"));

        if let Some(response) = block_response {
            // Submit a proposal response to the .signers contract for miners
            info!(
                "{self}: Broadcasting a block response to stacks node: {response:?}";
            );
            let accepted = matches!(response, BlockResponse::Accepted(..));
            match self
                .stackerdb
                .send_message_with_retry::<SignerMessage>(response.into())
            {
                Ok(_) => {
                    crate::monitoring::actions::increment_block_responses_sent(accepted);
                    if let Ok(Some(block_info)) = self
                        .signer_db
                        .block_lookup(&block_validate_response.signer_signature_hash())
                    {
                        crate::monitoring::actions::record_block_response_latency(
                            &block_info.block,
                        );
                    }
                }
                Err(e) => {
                    warn!("{self}: Failed to send block rejection to stacker-db: {e:?}",);
                }
            }
        };

        // Check if there is a pending block validation that we need to submit to the node
        match self.signer_db.get_and_remove_pending_block_validation() {
            Ok(Some(signer_sig_hash)) => {
                info!("{self}: Found a pending block validation: {signer_sig_hash:?}");
                match self.signer_db.block_lookup(&signer_sig_hash) {
                    Ok(Some(block_info)) => {
                        self.submit_block_for_validation(stacks_client, &block_info.block);
                    }
                    Ok(None) => {
                        // This should never happen
                        error!(
                            "{self}: Pending block validation not found in DB: {signer_sig_hash:?}"
                        );
                    }
                    Err(e) => error!("{self}: Failed to get block info: {e:?}"),
                }
            }
            Ok(None) => {}
            Err(e) => warn!("{self}: Failed to get pending block validation: {e:?}"),
        }
    }

    /// Check the current tracked submitted block proposal to see if it has timed out.
    /// Broadcasts a rejection and marks the block locally rejected if it has.
    fn check_submitted_block_proposal(&mut self) {
        let Some((proposal_signer_sighash, block_submission)) =
            self.submitted_block_proposal.take()
        else {
            // Nothing to check.
            return;
        };
        if block_submission.elapsed() < self.block_proposal_validation_timeout {
            // Not expired yet. Put it back!
            self.submitted_block_proposal = Some((proposal_signer_sighash, block_submission));
            return;
        }
        // For mutability reasons, we need to take the block_info out of the map and add it back after processing
        let mut block_info = match self.signer_db.block_lookup(&proposal_signer_sighash) {
            Ok(Some(block_info)) => {
                if block_info.has_reached_consensus() {
                    // The block has already reached consensus.
                    return;
                }
                block_info
            }
            Ok(None) => {
                // This is weird. If this is reached, its probably an error in code logic or the db was flushed.
                // Why are we tracking a block submission for a block we have never seen / stored before.
                error!("{self}: tracking an unknown block validation submission.";
                    "signer_sighash" => %proposal_signer_sighash,
                );
                return;
            }
            Err(e) => {
                error!("{self}: Failed to lookup block in signer db: {e:?}",);
                return;
            }
        };
        // We cannot determine the validity of the block, but we have not reached consensus on it yet.
        // Reject it so we aren't holding up the network because of our inaction.
        warn!(
            "{self}: Failed to receive block validation response within {} ms. Rejecting block.", self.block_proposal_validation_timeout.as_millis();
            "signer_sighash" => %proposal_signer_sighash,
        );
        let rejection = self.create_block_rejection(
            RejectReason::ConnectivityIssues(
                "failed to receive block validation response in time".to_string(),
            ),
            &block_info.block,
        );
        if let Err(e) = block_info.mark_locally_rejected() {
            if !block_info.has_reached_consensus() {
                warn!("{self}: Failed to mark block as locally rejected: {e:?}");
            }
        };
        debug!("{self}: Broadcasting a block response to stacks node: {rejection:?}");
        let res = self
            .stackerdb
            .send_message_with_retry::<SignerMessage>(rejection.into());

        crate::monitoring::actions::record_block_response_latency(&block_info.block);

        match res {
            Err(e) => warn!("{self}: Failed to send block rejection to stacker-db: {e:?}"),
            Ok(ack) if !ack.accepted => warn!(
                "{self}: Block rejection not accepted by stacker-db: {:?}",
                ack.reason
            ),
            Ok(_) => debug!("{self}: Block rejection accepted by stacker-db"),
        }
        self.signer_db
            .insert_block(&block_info)
            .unwrap_or_else(|e| self.handle_insert_block_error(e));
    }

    /// Compute the signing weight, given a list of signatures
    fn compute_signature_signing_weight<'a>(
        &self,
        addrs: impl Iterator<Item = &'a StacksAddress>,
    ) -> u32 {
        addrs.fold(0u32, |signing_weight, stacker_address| {
            let stacker_weight = self.signer_weights.get(stacker_address).unwrap_or(&0);
            signing_weight.saturating_add(*stacker_weight)
        })
    }

    /// Compute the total signing weight
    fn compute_signature_total_weight(&self) -> u32 {
        self.signer_weights
            .values()
            .fold(0u32, |acc, val| acc.saturating_add(*val))
    }

    /// Handle an observed rejection from another signer
    fn handle_block_rejection(&mut self, rejection: &BlockRejection) {
        debug!("{self}: Received a block-reject signature: {rejection:?}");

        let block_hash = &rejection.signer_signature_hash;
        let signature = &rejection.signature;

        let Some(mut block_info) = self.block_lookup_by_reward_cycle(block_hash) else {
            debug!(
                "{self}: Received block rejection for a block we have not seen before. Ignoring..."
            );
            return;
        };
        if block_info.has_reached_consensus() {
            debug!("{self}: Received block rejection for a block that is already marked as {}. Ignoring...", block_info.state);
            return;
        }

        // recover public key
        let Ok(public_key) = rejection.recover_public_key() else {
            debug!("{self}: Received block rejection with an unrecovarable signature. Will not store.";
               "block_hash" => %block_hash,
               "signature" => %signature
            );
            return;
        };

        let signer_address = StacksAddress::p2pkh(self.mainnet, &public_key);

        // authenticate the signature -- it must be signed by one of the stacking set
        let is_valid_sig = self.signer_addresses.iter().any(|addr| {
            // it only matters that the address hash bytes match
            signer_address.bytes() == addr.bytes()
        });

        if !is_valid_sig {
            debug!("{self}: Receive block rejection with an invalid signature. Will not store.";
                "block_hash" => %block_hash,
                "signature" => %signature
            );
            return;
        }

        // signature is valid! store it
        if let Err(e) = self
            .signer_db
            .add_block_rejection_signer_addr(block_hash, &signer_address)
        {
            warn!("{self}: Failed to save block rejection signature: {e:?}",);
        }

        // do we have enough signatures to mark a block a globally rejected?
        // i.e. is (set-size) - (threshold) + 1 reached.
        let rejection_addrs = match self.signer_db.get_block_rejection_signer_addrs(block_hash) {
            Ok(addrs) => addrs,
            Err(e) => {
                warn!("{self}: Failed to load block rejection addresses: {e:?}.",);
                return;
            }
        };
        let total_reject_weight = self.compute_signature_signing_weight(rejection_addrs.iter());
        let total_weight = self.compute_signature_total_weight();

        let min_weight = NakamotoBlockHeader::compute_voting_weight_threshold(total_weight)
            .unwrap_or_else(|_| {
                panic!("{self}: Failed to compute threshold weight for {total_weight}")
            });
        if total_reject_weight.saturating_add(min_weight) <= total_weight {
            // Not enough rejection signatures to make a decision
            return;
        }
        debug!("{self}: {total_reject_weight}/{total_weight} signers voted to reject the block {block_hash}");
        if let Err(e) = self.signer_db.mark_block_globally_rejected(&mut block_info) {
            warn!("{self}: Failed to mark block as globally rejected: {e:?}",);
        }
        if let Err(e) = self.signer_db.insert_block(&block_info) {
            error!("{self}: Failed to update block state: {e:?}",);
            panic!("{self} Failed to update block state: {e}");
        }
        if self
            .submitted_block_proposal
            .as_ref()
            .map(|(proposal_signer_sighash, _)| proposal_signer_sighash == block_hash)
            .unwrap_or(false)
        {
            // Consensus reached! No longer bother tracking its validation submission to the node as we are too late to participate in the decision anyway.
            self.submitted_block_proposal = None;
        }
    }

    /// Handle an observed signature from another signer
    fn handle_block_signature(&mut self, stacks_client: &StacksClient, accepted: &BlockAccepted) {
        let BlockAccepted {
            signer_signature_hash: block_hash,
            signature,
            metadata,
            ..
        } = accepted;
        debug!(
            "{self}: Received a block-accept signature: ({block_hash}, {signature}, {})",
            metadata.server_version
        );
        let Some(mut block_info) = self.block_lookup_by_reward_cycle(block_hash) else {
            debug!(
                "{self}: Received block signature for a block we have not seen before. Ignoring..."
            );
            return;
        };
        if block_info.has_reached_consensus() {
            debug!("{self}: Received block signature for a block that is already marked as {}. Ignoring...", block_info.state);
            return;
        }

        // recover public key
        let Ok(public_key) = Secp256k1PublicKey::recover_to_pubkey(block_hash.bits(), signature)
        else {
            debug!("{self}: Received unrecovarable signature. Will not store.";
                   "signature" => %signature,
                   "block_hash" => %block_hash);

            return;
        };

        // authenticate the signature -- it must be signed by one of the stacking set
        let is_valid_sig = self.signer_addresses.iter().any(|addr| {
            let stacker_address = StacksAddress::p2pkh(self.mainnet, &public_key);

            // it only matters that the address hash bytes match
            stacker_address.bytes() == addr.bytes()
        });

        if !is_valid_sig {
            debug!("{self}: Receive invalid signature {signature}. Will not store.");
            return;
        }

        // signature is valid! store it
        self.signer_db
            .add_block_signature(block_hash, signature)
            .unwrap_or_else(|_| panic!("{self}: Failed to save block signature"));

        // do we have enough signatures to broadcast?
        // i.e. is the threshold reached?
        let signatures = self
            .signer_db
            .get_block_signatures(block_hash)
            .unwrap_or_else(|_| panic!("{self}: Failed to load block signatures"));

        // put signatures in order by signer address (i.e. reward cycle order)
        let addrs_to_sigs: HashMap<_, _> = signatures
            .into_iter()
            .filter_map(|sig| {
                let Ok(public_key) = Secp256k1PublicKey::recover_to_pubkey(block_hash.bits(), &sig)
                else {
                    return None;
                };
                let addr = StacksAddress::p2pkh(self.mainnet, &public_key);
                Some((addr, sig))
            })
            .collect();

        let signature_weight = self.compute_signature_signing_weight(addrs_to_sigs.keys());
        let total_weight = self.compute_signature_total_weight();

        let min_weight = NakamotoBlockHeader::compute_voting_weight_threshold(total_weight)
            .unwrap_or_else(|_| {
                panic!("{self}: Failed to compute threshold weight for {total_weight}")
            });

        if min_weight > signature_weight {
            debug!(
                "{self}: Not enough signatures on block {} (have {}, need at least {}/{})",
                block_hash, signature_weight, min_weight, total_weight
            );
            return;
        }

        // have enough signatures to broadcast!
        // move block to LOCALLY accepted state.
        // It is only considered globally accepted IFF we receive a new block event confirming it OR see the chain tip of the node advance to it.
        if let Err(e) = block_info.mark_locally_accepted(true) {
            // Do not abort as we should still try to store the block signature threshold
            warn!("{self}: Failed to mark block as locally accepted: {e:?}");
        }
        let _ = self.signer_db.insert_block(&block_info).map_err(|e| {
            warn!(
                "Failed to set group threshold signature timestamp for {}: {:?}",
                block_hash, &e
            );
            panic!("{self} Failed to write block to signerdb: {e}");
        });
        #[cfg(any(test, feature = "testing"))]
        self.test_pause_block_broadcast(&block_info);

        self.broadcast_signed_block(stacks_client, block_info.block, &addrs_to_sigs);
        if self
            .submitted_block_proposal
            .as_ref()
            .map(|(proposal_hash, _)| proposal_hash == block_hash)
            .unwrap_or(false)
        {
            // Consensus reached! No longer bother tracking its validation submission to the node as we are too late to participate in the decision anyway.
            self.submitted_block_proposal = None;
        }
    }

    fn broadcast_signed_block(
        &self,
        stacks_client: &StacksClient,
        mut block: NakamotoBlock,
        addrs_to_sigs: &HashMap<StacksAddress, MessageSignature>,
    ) {
        let block_hash = block.header.signer_signature_hash();
        // collect signatures for the block
        let signatures: Vec<_> = self
            .signer_addresses
            .iter()
            .filter_map(|addr| addrs_to_sigs.get(addr).cloned())
            .collect();

        block.header.signer_signature_hash();
        block.header.signer_signature = signatures;

        #[cfg(any(test, feature = "testing"))]
        if self.test_skip_block_broadcast(&block) {
            return;
        }
        debug!(
            "{self}: Broadcasting Stacks block {} to node",
            &block.block_id()
        );
        stacks_client.post_block_until_ok(self, &block);

        if let Err(e) = self
            .signer_db
            .set_block_broadcasted(&block_hash, get_epoch_time_secs())
        {
            warn!("{self}: Failed to set block broadcasted for {block_hash}: {e:?}");
        }
    }

    /// Submit a block for validation, and mark it as pending if the node
    /// is busy with a previous request.
    fn submit_block_for_validation(&mut self, stacks_client: &StacksClient, block: &NakamotoBlock) {
        let signer_signature_hash = block.header.signer_signature_hash();
        match stacks_client.submit_block_for_validation(block.clone()) {
            Ok(_) => {
                self.submitted_block_proposal = Some((signer_signature_hash, Instant::now()));
            }
            Err(ClientError::RequestFailure(status)) => {
                if status.as_u16() == TOO_MANY_REQUESTS_STATUS {
                    info!("{self}: Received 429 from stacks node for block validation request. Inserting pending block validation...";
                        "signer_signature_hash" => %signer_signature_hash,
                    );
                    self.signer_db
                        .insert_pending_block_validation(
                            &signer_signature_hash,
                            get_epoch_time_secs(),
                        )
                        .unwrap_or_else(|e| {
                            warn!("{self}: Failed to insert pending block validation: {e:?}")
                        });
                } else {
                    warn!("{self}: Received non-429 status from stacks node: {status}");
                }
            }
            Err(e) => {
                warn!("{self}: Failed to submit block for validation: {e:?}");
            }
        }
    }

    /// Send a mock signature to stackerdb to prove we are still alive
    fn mock_sign(&mut self, mock_proposal: MockProposal) {
        info!("{self}: Mock signing mock proposal: {mock_proposal:?}");
        let mock_signature = MockSignature::new(mock_proposal, &self.private_key);
        let message = SignerMessage::MockSignature(mock_signature);
        if let Err(e) = self
            .stackerdb
            .send_message_with_retry::<SignerMessage>(message)
        {
            warn!("{self}: Failed to send mock signature to stacker-db: {e:?}",);
        }
    }

    /// Helper for logging insert_block error
    pub fn handle_insert_block_error(&self, e: DBError) {
        error!("{self}: Failed to insert block into signer-db: {e:?}");
        panic!("{self} Failed to write block to signerdb: {e}");
    }

    /// Helper for getting the block info from the db while accommodating for reward cycle
    pub fn block_lookup_by_reward_cycle(
        &self,
        block_hash: &Sha512Trunc256Sum,
    ) -> Option<BlockInfo> {
        let block_info = self
            .signer_db
            .block_lookup(block_hash)
            .inspect_err(|e| {
                error!("{self}: Failed to lookup block hash {block_hash} in signer db: {e:?}");
            })
            .ok()
            .flatten()?;
        if block_info.reward_cycle == self.reward_cycle {
            Some(block_info)
        } else {
            None
        }
    }
}
