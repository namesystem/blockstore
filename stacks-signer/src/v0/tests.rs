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

use std::sync::LazyLock;

use blockstack_lib::chainstate::nakamoto::NakamotoBlock;
use libsigner::v0::messages::{BlockResponse, RejectReason};
use libsigner::BlockProposal;
use slog::{slog_info, slog_warn};
use stacks_common::types::chainstate::StacksPublicKey;
use stacks_common::util::get_epoch_time_secs;
use stacks_common::util::tests::TestFlag;
use stacks_common::{info, warn};

use super::signer::Signer;
use crate::signerdb::BlockInfo;

/// A global variable that can be used to reject all block proposals if the signer's public key is in the provided list
pub static TEST_REJECT_ALL_BLOCK_PROPOSAL: LazyLock<TestFlag<Vec<StacksPublicKey>>> =
    LazyLock::new(TestFlag::default);

/// A global variable that can be used to ignore block proposals if the signer's public key is in the provided list
pub static TEST_IGNORE_ALL_BLOCK_PROPOSALS: LazyLock<TestFlag<Vec<StacksPublicKey>>> =
    LazyLock::new(TestFlag::default);

/// A global variable that can be used to pause broadcasting the block to the network
pub static TEST_PAUSE_BLOCK_BROADCAST: LazyLock<TestFlag<bool>> = LazyLock::new(TestFlag::default);

/// A global variable that can be used to skip broadcasting the block to the network
pub static TEST_SKIP_BLOCK_BROADCAST: LazyLock<TestFlag<bool>> = LazyLock::new(TestFlag::default);

/// A global variable that can be used to pause the block validation submission
pub static TEST_STALL_BLOCK_VALIDATION_SUBMISSION: LazyLock<TestFlag<bool>> =
    LazyLock::new(TestFlag::default);

/// A global variable that can be used to prevent signer cleanup
pub static TEST_SKIP_SIGNER_CLEANUP: LazyLock<TestFlag<bool>> = LazyLock::new(TestFlag::default);

impl Signer {
    /// Skip the block broadcast if the TEST_SKIP_BLOCK_BROADCAST flag is set
    pub fn test_skip_block_broadcast(&self, block: &NakamotoBlock) -> bool {
        if TEST_SKIP_BLOCK_BROADCAST.get() {
            let block_hash = block.header.signer_signature_hash();
            warn!(
                "{self}: Skipping block broadcast due to testing directive";
                "block_id" => %block.block_id(),
                "height" => block.header.chain_length,
                "consensus_hash" => %block.header.consensus_hash
            );

            if let Err(e) = self
                .signer_db
                .set_block_broadcasted(&block_hash, get_epoch_time_secs())
            {
                warn!("{self}: Failed to set block broadcasted for {block_hash}: {e:?}");
            }
            return true;
        }
        false
    }

    /// Reject block proposals if the TEST_REJECT_ALL_BLOCK_PROPOSAL flag is set for the signer's public key
    pub fn test_reject_block_proposal(
        &mut self,
        block_proposal: &BlockProposal,
        block_info: &mut BlockInfo,
        block_response: Option<BlockResponse>,
    ) -> Option<BlockResponse> {
        let public_keys = TEST_REJECT_ALL_BLOCK_PROPOSAL.get();
        if public_keys.contains(
            &stacks_common::types::chainstate::StacksPublicKey::from_private(&self.private_key),
        ) {
            warn!("{self}: Rejecting block proposal automatically due to testing directive";
                "block_id" => %block_proposal.block.block_id(),
                "height" => block_proposal.block.header.chain_length,
                "consensus_hash" => %block_proposal.block.header.consensus_hash
            );
            if let Err(e) = block_info.mark_locally_rejected() {
                if !block_info.has_reached_consensus() {
                    warn!("{self}: Failed to mark block as locally rejected: {e:?}");
                }
            };
            // We must insert the block into the DB to prevent subsequent repeat proposals being accepted (should reject
            // as invalid since we rejected in a prior round if this crops up again)
            // in case this is the first time we saw this block. Safe to do since this is testing case only.
            self.signer_db
                .insert_block(block_info)
                .unwrap_or_else(|e| self.handle_insert_block_error(e));
            Some(self.create_block_rejection(RejectReason::TestingDirective, &block_proposal.block))
        } else {
            block_response
        }
    }

    /// Pause the block broadcast if the TEST_PAUSE_BLOCK_BROADCAST flag is set
    pub fn test_pause_block_broadcast(&self, block_info: &BlockInfo) {
        if TEST_PAUSE_BLOCK_BROADCAST.get() {
            // Do an extra check just so we don't log EVERY time.
            warn!("{self}: Block broadcast is stalled due to testing directive.";
                "block_id" => %block_info.block.block_id(),
                "height" => block_info.block.header.chain_length,
            );
            while TEST_PAUSE_BLOCK_BROADCAST.get() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            info!("{self}: Block validation is no longer stalled due to testing directive.";
                "block_id" => %block_info.block.block_id(),
                "height" => block_info.block.header.chain_length,
            );
        }
    }

    /// Ignore block proposals if the TEST_IGNORE_ALL_BLOCK_PROPOSALS flag is set for the signer's public key
    pub fn test_ignore_all_block_proposals(&self, block_proposal: &BlockProposal) -> bool {
        let public_keys = TEST_IGNORE_ALL_BLOCK_PROPOSALS.get();
        if public_keys.contains(
            &stacks_common::types::chainstate::StacksPublicKey::from_private(&self.private_key),
        ) {
            warn!("{self}: Ignoring block proposal due to testing directive";
                "block_id" => %block_proposal.block.block_id(),
                "height" => block_proposal.block.header.chain_length,
                "consensus_hash" => %block_proposal.block.header.consensus_hash
            );
            return true;
        }
        false
    }

    /// Stall the block validation submission if the TEST_STALL_BLOCK_VALIDATION_SUBMISSION flag is set
    pub fn test_stall_block_validation_submission(&self) {
        if TEST_STALL_BLOCK_VALIDATION_SUBMISSION.get() {
            // Do an extra check just so we don't log EVERY time.
            warn!("{self}: Block validation submission is stalled due to testing directive");
            while TEST_STALL_BLOCK_VALIDATION_SUBMISSION.get() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            warn!("{self}: Block validation submission is no longer stalled due to testing directive. Continuing...");
        }
    }
}
