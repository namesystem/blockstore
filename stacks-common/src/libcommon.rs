#![allow(unused_macros)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![cfg_attr(test, allow(unused_variables, unused_assignments))]
#![allow(clippy::assertions_on_constants)]

#[cfg(feature = "log")]
#[macro_use(o, slog_log, slog_trace, slog_debug, slog_info, slog_warn, slog_error)]
extern crate slog;

#[macro_use]
extern crate serde_derive;

#[cfg(unix)]
extern crate nix;

#[cfg(windows)]
extern crate winapi;

#[macro_use]
pub mod util;

#[macro_use]
pub mod codec;

pub mod types;

pub mod address;

pub mod deps_common;

#[cfg(not(feature = "wasm"))]
pub mod bitvec;

use crate::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, SortitionId, StacksBlockId};

pub mod consts {
    use crate::types::chainstate::{BlockHeaderHash, ConsensusHash};
    pub use crate::types::MINING_COMMITMENT_WINDOW;

    pub const TOKEN_TRANSFER_MEMO_LENGTH: usize = 34; // same as it is in Stacks v1

    pub const BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT: u64 = 0;
    pub const BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP: u32 = 0;
    pub const BITCOIN_REGTEST_FIRST_BLOCK_HASH: &str =
        "0000000000000000000000000000000000000000000000000000000000000000";

    pub const FIRST_STACKS_BLOCK_HASH: BlockHeaderHash = BlockHeaderHash([0u8; 32]);

    pub const FIRST_BURNCHAIN_CONSENSUS_HASH: ConsensusHash = ConsensusHash([0u8; 20]);

    pub const CHAIN_ID_MAINNET: u32 = 0x00000001;
    pub const CHAIN_ID_TESTNET: u32 = 0x80000000;

    #[cfg(any(test, feature = "testing"))]
    pub const MINER_REWARD_MATURITY: u64 = 2; // small for testing purposes

    #[cfg(not(any(test, feature = "testing")))]
    pub const MINER_REWARD_MATURITY: u64 = 100;

    pub const STACKS_EPOCH_MAX: u64 = i64::MAX as u64;

    /// The number of StackerDB slots each signing key needs
    ///  to use to participate in DKG and block validation signing.
    pub const SIGNER_SLOTS_PER_USER: u32 = 13;

    /// peer version (big-endian)
    /// first byte == major network protocol version (currently 0x18)
    /// second and third bytes are unused
    /// fourth byte == highest epoch supported by this node
    pub const PEER_VERSION_MAINNET_MAJOR: u32 = 0x18000000;
    pub const PEER_VERSION_TESTNET_MAJOR: u32 = 0xfacade00;

    pub const PEER_VERSION_EPOCH_1_0: u8 = 0x00;
    pub const PEER_VERSION_EPOCH_2_0: u8 = 0x00;
    pub const PEER_VERSION_EPOCH_2_05: u8 = 0x05;
    pub const PEER_VERSION_EPOCH_2_1: u8 = 0x06;
    pub const PEER_VERSION_EPOCH_2_2: u8 = 0x07;
    pub const PEER_VERSION_EPOCH_2_3: u8 = 0x08;
    pub const PEER_VERSION_EPOCH_2_4: u8 = 0x09;
    pub const PEER_VERSION_EPOCH_2_5: u8 = 0x0a;
    pub const PEER_VERSION_EPOCH_3_0: u8 = 0x0b;
    pub const PEER_VERSION_EPOCH_3_1: u8 = 0x0c;

    /// this should be updated to the latest network epoch version supported by
    ///  this node. this will be checked by the `validate_epochs()` method.
    pub const PEER_NETWORK_EPOCH: u32 = PEER_VERSION_EPOCH_3_1 as u32;

    /// set the fourth byte of the peer version
    pub const PEER_VERSION_MAINNET: u32 = PEER_VERSION_MAINNET_MAJOR | PEER_NETWORK_EPOCH;
    pub const PEER_VERSION_TESTNET: u32 = PEER_VERSION_TESTNET_MAJOR | PEER_NETWORK_EPOCH;

    /// network identifiers
    pub const NETWORK_ID_MAINNET: u32 = 0x17000000;
    pub const NETWORK_ID_TESTNET: u32 = 0xff000000;

    /// number of uSTX per STX
    pub const MICROSTACKS_PER_STACKS: u32 = 1_000_000;
}

/// This test asserts that the constant above doesn't change.
/// This exists because the constant above is used by Epoch 2.5 instantiation code.
///
/// Adding more slots will require instantiating more .signers contracts through either
///  consensus changes (i.e., a new epoch) or through non-consensus-critical contract
///  deployments.
#[test]
fn signer_slots_count_2_5() {
    assert_eq!(
        consts::SIGNER_SLOTS_PER_USER,
        13,
        "The .signers-x-y contracts in Epoch 2.5 were instantiated with 13 slots"
    );
}
