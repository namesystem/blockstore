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

use std::fmt::{Debug, Display};
use std::fs;
use std::net::{SocketAddr, ToSocketAddrs};
use std::path::PathBuf;
use std::time::Duration;

use blockstack_lib::chainstate::stacks::TransactionVersion;
use clarity::util::hash::to_hex;
use libsigner::SignerEntries;
use serde::Deserialize;
use stacks_common::address::{
    C32_ADDRESS_VERSION_MAINNET_SINGLESIG, C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
};
use stacks_common::consts::{CHAIN_ID_MAINNET, CHAIN_ID_TESTNET};
use stacks_common::types::chainstate::{StacksAddress, StacksPrivateKey, StacksPublicKey};
use stacks_common::types::PrivateKey;
use stacks_common::util::hash::Hash160;
use wsts::curve::scalar::Scalar;

use crate::client::SignerSlotID;

const EVENT_TIMEOUT_MS: u64 = 5000;
const BLOCK_PROPOSAL_TIMEOUT_MS: u64 = 45_000;
// Default transaction fee to use in microstacks (if unspecificed in the config file)
const TX_FEE_USTX: u64 = 10_000;

#[derive(thiserror::Error, Debug)]
/// An error occurred parsing the provided configuration
pub enum ConfigError {
    /// Error occurred reading config file
    #[error("{0}")]
    InvalidConfig(String),
    /// An error occurred parsing the TOML data
    #[error("{0}")]
    ParseError(String),
    /// A field was malformed
    #[error("identifier={0}, value={1}")]
    BadField(String, String),
    /// An unsupported address version
    #[error("Failed to convert private key to address: unsupported address version.")]
    UnsupportedAddressVersion,
}

#[derive(serde::Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
/// The Stacks network to use.
pub enum Network {
    /// The mainnet network
    Mainnet,
    /// The testnet network
    Testnet,
    /// The mocknet network
    Mocknet,
}

impl std::fmt::Display for Network {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mainnet => write!(f, "mainnet"),
            Self::Testnet => write!(f, "testnet"),
            Self::Mocknet => write!(f, "mocknet"),
        }
    }
}

impl Network {
    /// Converts a Network enum variant to a corresponding chain id
    pub const fn to_chain_id(&self) -> u32 {
        match self {
            Self::Mainnet => CHAIN_ID_MAINNET,
            Self::Testnet | Self::Mocknet => CHAIN_ID_TESTNET,
        }
    }

    /// Convert a Network enum variant to a corresponding address version
    pub const fn to_address_version(&self) -> u8 {
        match self {
            Self::Mainnet => C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
            Self::Testnet | Self::Mocknet => C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        }
    }

    /// Convert a Network enum variant to a Transaction Version
    pub const fn to_transaction_version(&self) -> TransactionVersion {
        match self {
            Self::Mainnet => TransactionVersion::Mainnet,
            Self::Testnet | Self::Mocknet => TransactionVersion::Testnet,
        }
    }

    /// Check if the network is Mainnet or not
    pub const fn is_mainnet(&self) -> bool {
        match self {
            Self::Mainnet => true,
            Self::Testnet | Self::Mocknet => false,
        }
    }
}

/// The Configuration info needed for an individual signer per reward cycle
#[derive(Debug, Clone)]
pub struct SignerConfig {
    /// The reward cycle of the configuration
    pub reward_cycle: u64,
    /// The signer ID assigned to this signer to be used in DKG and Sign rounds
    pub signer_id: u32,
    /// The signer stackerdb slot id (may be different from signer_id)
    pub signer_slot_id: SignerSlotID,
    /// This signer's key ids
    pub key_ids: Vec<u32>,
    /// The registered signers for this reward cycle
    pub signer_entries: SignerEntries,
    /// The signer slot ids of all signers registered for this reward cycle
    pub signer_slot_ids: Vec<SignerSlotID>,
    /// The Scalar representation of the private key for signer communication
    pub ecdsa_private_key: Scalar,
    /// The private key for this signer
    pub stacks_private_key: StacksPrivateKey,
    /// The node host for this signer
    pub node_host: String,
    /// Whether this signer is running on mainnet or not
    pub mainnet: bool,
    /// timeout to gather DkgPublicShares messages
    pub dkg_public_timeout: Option<Duration>,
    /// timeout to gather DkgPrivateShares messages
    pub dkg_private_timeout: Option<Duration>,
    /// timeout to gather DkgEnd messages
    pub dkg_end_timeout: Option<Duration>,
    /// timeout to gather nonces
    pub nonce_timeout: Option<Duration>,
    /// timeout to gather signature shares
    pub sign_timeout: Option<Duration>,
    /// the STX tx fee to use in uSTX.
    pub tx_fee_ustx: u64,
    /// If set, will use the estimated fee up to this amount.
    pub max_tx_fee_ustx: Option<u64>,
    /// The path to the signer's database file
    pub db_path: PathBuf,
    /// How much time must pass between the first block proposal in a tenure and the next bitcoin block
    ///  before a subsequent miner isn't allowed to reorg the tenure
    pub first_proposal_burn_block_timing: Duration,
    /// How much time to wait for a miner to propose a block following a sortition
    pub block_proposal_timeout: Duration,
    /// Broadcast a block to the node if we gather enough signatures from other signers
    pub broadcast_signed_blocks: bool,
}

/// The parsed configuration for the signer
#[derive(Clone)]
pub struct GlobalConfig {
    /// endpoint to the stacks node
    pub node_host: String,
    /// endpoint to the event receiver
    pub endpoint: SocketAddr,
    /// The Scalar representation of the private key for signer communication
    pub ecdsa_private_key: Scalar,
    /// The signer's Stacks private key
    pub stacks_private_key: StacksPrivateKey,
    /// The signer's Stacks address
    pub stacks_address: StacksAddress,
    /// The network to use. One of "mainnet" or "testnet".
    pub network: Network,
    /// The time to wait for a response from the stacker-db instance
    pub event_timeout: Duration,
    /// timeout to gather DkgPublicShares messages
    pub dkg_public_timeout: Option<Duration>,
    /// timeout to gather DkgPrivateShares messages
    pub dkg_private_timeout: Option<Duration>,
    /// timeout to gather DkgEnd messages
    pub dkg_end_timeout: Option<Duration>,
    /// timeout to gather nonces
    pub nonce_timeout: Option<Duration>,
    /// timeout to gather signature shares
    pub sign_timeout: Option<Duration>,
    /// the STX tx fee to use in uSTX.
    pub tx_fee_ustx: u64,
    /// the max STX tx fee to use in uSTX when estimating fees
    pub max_tx_fee_ustx: Option<u64>,
    /// the authorization password for the block proposal endpoint
    pub auth_password: String,
    /// The path to the signer's database file
    pub db_path: PathBuf,
    /// Metrics endpoint
    pub metrics_endpoint: Option<SocketAddr>,
    /// How much time between the first block proposal in a tenure and the next bitcoin block
    ///  must pass before a subsequent miner isn't allowed to reorg the tenure
    pub first_proposal_burn_block_timing: Duration,
    /// How much time to wait for a miner to propose a block following a sortition
    pub block_proposal_timeout: Duration,
    /// Broadcast a block to the node if we gather enough signatures from other signers
    pub broadcast_signed_blocks: bool,
}

/// Internal struct for loading up the config file
#[derive(Deserialize, Debug)]
struct RawConfigFile {
    /// endpoint to stacks node
    pub node_host: String,
    /// endpoint to event receiver
    pub endpoint: String,
    /// The hex representation of the signer's Stacks private key used for communicating
    /// with the Stacks Node, including writing to the Stacker DB instance.
    pub stacks_private_key: String,
    /// The network to use. One of "mainnet" or "testnet".
    pub network: Network,
    /// The time to wait (in millisecs) for a response from the stacker-db instance
    pub event_timeout_ms: Option<u64>,
    /// timeout in (millisecs) to gather DkgPublicShares messages
    pub dkg_public_timeout_ms: Option<u64>,
    /// timeout in (millisecs) to gather DkgPrivateShares messages
    pub dkg_private_timeout_ms: Option<u64>,
    /// timeout in (millisecs) to gather DkgEnd messages
    pub dkg_end_timeout_ms: Option<u64>,
    /// timeout in (millisecs) to gather nonces
    pub nonce_timeout_ms: Option<u64>,
    /// timeout in (millisecs) to gather signature shares
    pub sign_timeout_ms: Option<u64>,
    /// the STX tx fee to use in uSTX. If not set, will default to TX_FEE_USTX
    pub tx_fee_ustx: Option<u64>,
    /// the max STX tx fee to use in uSTX when estimating fees.
    /// If not set, will use tx_fee_ustx.
    pub max_tx_fee_ustx: Option<u64>,
    /// The authorization password for the block proposal endpoint
    pub auth_password: String,
    /// The path to the signer's database file or :memory: for an in-memory database
    pub db_path: String,
    /// Metrics endpoint
    pub metrics_endpoint: Option<String>,
    /// How much time must pass between the first block proposal in a tenure and the next bitcoin block
    ///  before a subsequent miner isn't allowed to reorg the tenure
    pub first_proposal_burn_block_timing_secs: Option<u64>,
    /// How much time to wait for a miner to propose a block following a sortition in milliseconds
    pub block_proposal_timeout_ms: Option<u64>,
}

impl RawConfigFile {
    /// load the config from a string
    pub fn load_from_str(data: &str) -> Result<Self, ConfigError> {
        let config: Self =
            toml::from_str(data).map_err(|e| ConfigError::ParseError(format!("{e:?}")))?;
        Ok(config)
    }
    /// load the config from a file and parse it
    #[allow(dead_code)]
    pub fn load_from_file(path: &str) -> Result<Self, ConfigError> {
        Self::try_from(&PathBuf::from(path))
    }
}

impl TryFrom<&PathBuf> for RawConfigFile {
    type Error = ConfigError;

    fn try_from(path: &PathBuf) -> Result<Self, Self::Error> {
        Self::load_from_str(&fs::read_to_string(path).map_err(|e| {
            ConfigError::InvalidConfig(format!("failed to read config file: {e:?}"))
        })?)
    }
}

impl TryFrom<RawConfigFile> for GlobalConfig {
    type Error = ConfigError;

    /// Attempt to decode the raw config file's primitive types into our types.
    /// NOTE: network access is required for this to work
    fn try_from(raw_data: RawConfigFile) -> Result<Self, Self::Error> {
        url::Url::parse(&format!("http://{}", raw_data.node_host)).map_err(|_| {
            ConfigError::BadField("node_host".to_string(), raw_data.node_host.clone())
        })?;

        let endpoint = raw_data
            .endpoint
            .to_socket_addrs()
            .map_err(|_| ConfigError::BadField("endpoint".to_string(), raw_data.endpoint.clone()))?
            .next()
            .ok_or_else(|| {
                ConfigError::BadField("endpoint".to_string(), raw_data.endpoint.clone())
            })?;

        let stacks_private_key =
            StacksPrivateKey::from_hex(&raw_data.stacks_private_key).map_err(|_| {
                ConfigError::BadField(
                    "stacks_private_key".to_string(),
                    raw_data.stacks_private_key.clone(),
                )
            })?;

        let ecdsa_private_key =
            Scalar::try_from(&stacks_private_key.to_bytes()[..32]).map_err(|_| {
                ConfigError::BadField(
                    "stacks_private_key".to_string(),
                    raw_data.stacks_private_key.clone(),
                )
            })?;
        let stacks_public_key = StacksPublicKey::from_private(&stacks_private_key);
        let signer_hash = Hash160::from_data(stacks_public_key.to_bytes_compressed().as_slice());
        let stacks_address =
            StacksAddress::p2pkh_from_hash(raw_data.network.is_mainnet(), signer_hash);
        let event_timeout =
            Duration::from_millis(raw_data.event_timeout_ms.unwrap_or(EVENT_TIMEOUT_MS));
        let dkg_end_timeout = raw_data.dkg_end_timeout_ms.map(Duration::from_millis);
        let dkg_public_timeout = raw_data.dkg_public_timeout_ms.map(Duration::from_millis);
        let dkg_private_timeout = raw_data.dkg_private_timeout_ms.map(Duration::from_millis);
        let nonce_timeout = raw_data.nonce_timeout_ms.map(Duration::from_millis);
        let sign_timeout = raw_data.sign_timeout_ms.map(Duration::from_millis);
        let first_proposal_burn_block_timing =
            Duration::from_secs(raw_data.first_proposal_burn_block_timing_secs.unwrap_or(30));
        let db_path = raw_data.db_path.into();

        let metrics_endpoint = match raw_data.metrics_endpoint {
            Some(endpoint) => Some(
                endpoint
                    .to_socket_addrs()
                    .map_err(|_| ConfigError::BadField("endpoint".to_string(), endpoint.clone()))?
                    .next()
                    .ok_or_else(|| {
                        ConfigError::BadField("endpoint".to_string(), endpoint.clone())
                    })?,
            ),
            None => None,
        };

        let block_proposal_timeout = Duration::from_millis(
            raw_data
                .block_proposal_timeout_ms
                .unwrap_or(BLOCK_PROPOSAL_TIMEOUT_MS),
        );

        Ok(Self {
            node_host: raw_data.node_host,
            endpoint,
            stacks_private_key,
            ecdsa_private_key,
            stacks_address,
            network: raw_data.network,
            event_timeout,
            dkg_end_timeout,
            dkg_public_timeout,
            dkg_private_timeout,
            nonce_timeout,
            sign_timeout,
            tx_fee_ustx: raw_data.tx_fee_ustx.unwrap_or(TX_FEE_USTX),
            max_tx_fee_ustx: raw_data.max_tx_fee_ustx,
            auth_password: raw_data.auth_password,
            db_path,
            metrics_endpoint,
            first_proposal_burn_block_timing,
            block_proposal_timeout,
            broadcast_signed_blocks: true,
        })
    }
}

impl TryFrom<&PathBuf> for GlobalConfig {
    type Error = ConfigError;
    fn try_from(path: &PathBuf) -> Result<Self, ConfigError> {
        let config_file = RawConfigFile::try_from(path)?;
        Self::try_from(config_file)
    }
}

impl GlobalConfig {
    /// load the config from a string and parse it
    pub fn load_from_str(data: &str) -> Result<Self, ConfigError> {
        RawConfigFile::load_from_str(data)?.try_into()
    }

    /// load the config from a file and parse it
    pub fn load_from_file(path: &str) -> Result<Self, ConfigError> {
        Self::try_from(&PathBuf::from(path))
    }

    /// Return a string with non-sensitive configuration
    /// information for logging purposes
    pub fn config_to_log_string(&self) -> String {
        let tx_fee = match self.tx_fee_ustx {
            0 => "default".to_string(),
            _ => (self.tx_fee_ustx as f64 / 1_000_000.0).to_string(),
        };
        let metrics_endpoint = match &self.metrics_endpoint {
            Some(endpoint) => endpoint.to_string(),
            None => "None".to_string(),
        };
        format!(
            r#"
Stacks node host: {node_host}
Signer endpoint: {endpoint}
Stacks address: {stacks_address}
Public key: {public_key}
Network: {network}
Database path: {db_path}
DKG transaction fee: {tx_fee} uSTX
Metrics endpoint: {metrics_endpoint}
"#,
            node_host = self.node_host,
            endpoint = self.endpoint,
            stacks_address = self.stacks_address,
            public_key = to_hex(
                &StacksPublicKey::from_private(&self.stacks_private_key).to_bytes_compressed()
            ),
            network = self.network,
            db_path = self.db_path.to_str().unwrap_or_default(),
            tx_fee = tx_fee,
            metrics_endpoint = metrics_endpoint,
        )
    }
}

impl Display for GlobalConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.config_to_log_string())
    }
}

impl Debug for GlobalConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.config_to_log_string())
    }
}

/// Helper function for building a signer config for each provided signer private key
#[allow(clippy::too_many_arguments)]
pub fn build_signer_config_tomls(
    stacks_private_keys: &[StacksPrivateKey],
    node_host: &str,
    timeout: Option<Duration>,
    network: &Network,
    password: &str,
    run_stamp: u16,
    mut port_start: usize,
    max_tx_fee_ustx: Option<u64>,
    tx_fee_ustx: Option<u64>,
    mut metrics_port_start: Option<usize>,
) -> Vec<String> {
    let mut signer_config_tomls = vec![];

    for stacks_private_key in stacks_private_keys {
        let endpoint = format!("localhost:{}", port_start);
        port_start += 1;

        let stacks_public_key = StacksPublicKey::from_private(stacks_private_key).to_hex();
        let db_dir = format!(
            "/tmp/stacks-node-tests/integrations-signers/{run_stamp}/signer_{stacks_public_key}"
        );
        let db_path = format!("{db_dir}/signerdb.sqlite");
        fs::create_dir_all(&db_dir).unwrap();

        let stacks_private_key = stacks_private_key.to_hex();
        let mut signer_config_toml = format!(
            r#"
stacks_private_key = "{stacks_private_key}"
node_host = "{node_host}"
endpoint = "{endpoint}"
network = "{network}"
auth_password = "{password}"
db_path = "{db_path}"
"#
        );

        if let Some(timeout) = timeout {
            let event_timeout_ms = timeout.as_millis();
            signer_config_toml = format!(
                r#"
{signer_config_toml}
event_timeout = {event_timeout_ms}
"#
            )
        }

        if let Some(max_tx_fee_ustx) = max_tx_fee_ustx {
            signer_config_toml = format!(
                r#"
{signer_config_toml}
max_tx_fee_ustx = {max_tx_fee_ustx}
"#
            )
        }

        if let Some(tx_fee_ustx) = tx_fee_ustx {
            signer_config_toml = format!(
                r#"
{signer_config_toml}
tx_fee_ustx = {tx_fee_ustx}
"#
            )
        }

        if let Some(metrics_port) = metrics_port_start {
            let metrics_endpoint = format!("localhost:{}", metrics_port);
            signer_config_toml = format!(
                r#"
{signer_config_toml}
metrics_endpoint = "{metrics_endpoint}"
"#
            );
            metrics_port_start = Some(metrics_port + 1);
        }

        signer_config_tomls.push(signer_config_toml);
    }

    signer_config_tomls
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_signer_config_tomls_should_produce_deserializable_strings() {
        let pk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let node_host = "localhost";
        let network = Network::Testnet;
        let password = "melon";

        let config_tomls = build_signer_config_tomls(
            &[pk],
            node_host,
            None,
            &network,
            password,
            rand::random(),
            3000,
            None,
            None,
            Some(4000),
        );

        let config =
            RawConfigFile::load_from_str(&config_tomls[0]).expect("Failed to parse config file");

        assert_eq!(config.auth_password, "melon");
        assert!(config.max_tx_fee_ustx.is_none());
        assert!(config.tx_fee_ustx.is_none());
        assert_eq!(config.metrics_endpoint, Some("localhost:4000".to_string()));
    }

    #[test]
    fn fee_options_should_deserialize_correctly() {
        let pk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let node_host = "localhost";
        let network = Network::Testnet;
        let password = "melon";

        // Test both max_tx_fee_ustx and tx_fee_ustx are unspecified
        let config_tomls = build_signer_config_tomls(
            &[pk],
            node_host,
            None,
            &network,
            password,
            rand::random(),
            3000,
            None,
            None,
            None,
        );

        let config =
            RawConfigFile::load_from_str(&config_tomls[0]).expect("Failed to parse config file");

        assert!(config.max_tx_fee_ustx.is_none());
        assert!(config.tx_fee_ustx.is_none());

        let config = GlobalConfig::try_from(config).expect("Failed to parse config");
        assert!(config.max_tx_fee_ustx.is_none());
        assert_eq!(config.tx_fee_ustx, TX_FEE_USTX);

        // Test both max_tx_fee_ustx and tx_fee_ustx are specified
        let max_tx_fee_ustx = Some(1000);
        let tx_fee_ustx = Some(2000);
        let config_tomls = build_signer_config_tomls(
            &[pk],
            node_host,
            None,
            &network,
            password,
            rand::random(),
            3000,
            max_tx_fee_ustx,
            tx_fee_ustx,
            None,
        );

        let config =
            RawConfigFile::load_from_str(&config_tomls[0]).expect("Failed to parse config file");

        assert_eq!(config.max_tx_fee_ustx, max_tx_fee_ustx);
        assert_eq!(config.tx_fee_ustx, tx_fee_ustx);

        // Test only max_tx_fee_ustx is specified
        let max_tx_fee_ustx = Some(1000);
        let config_tomls = build_signer_config_tomls(
            &[pk],
            node_host,
            None,
            &network,
            password,
            rand::random(),
            3000,
            max_tx_fee_ustx,
            None,
            None,
        );

        let config =
            RawConfigFile::load_from_str(&config_tomls[0]).expect("Failed to parse config file");

        assert_eq!(config.max_tx_fee_ustx, max_tx_fee_ustx);
        assert!(config.tx_fee_ustx.is_none());

        let config = GlobalConfig::try_from(config).expect("Failed to parse config");
        assert_eq!(config.max_tx_fee_ustx, max_tx_fee_ustx);
        assert_eq!(config.tx_fee_ustx, TX_FEE_USTX);

        // Test only tx_fee_ustx is specified
        let tx_fee_ustx = Some(1000);
        let config_tomls = build_signer_config_tomls(
            &[pk],
            node_host,
            None,
            &network,
            password,
            rand::random(),
            3000,
            None,
            tx_fee_ustx,
            None,
        );

        let config =
            RawConfigFile::load_from_str(&config_tomls[0]).expect("Failed to parse config file");

        assert!(config.max_tx_fee_ustx.is_none());
        assert_eq!(config.tx_fee_ustx, tx_fee_ustx);

        let config = GlobalConfig::try_from(config).expect("Failed to parse config");
        assert!(config.max_tx_fee_ustx.is_none());
        assert_eq!(Some(config.tx_fee_ustx), tx_fee_ustx);
    }

    #[test]
    fn test_config_to_string() {
        let config = GlobalConfig::load_from_file("./src/tests/conf/signer-0.toml").unwrap();
        let config_str = config.config_to_log_string();

        let expected_str_v4 = r#"
Stacks node host: 127.0.0.1:20443
Signer endpoint: 127.0.0.1:30000
Stacks address: ST3FPN8KBZ3YPBP0ZJGAAHTVFMQDTJCR5QPS7VTNJ
Public key: 03bc489f27da3701d9f9e577c88de5567cf4023111b7577042d55cde4d823a3505
Network: testnet
Database path: :memory:
DKG transaction fee: 0.01 uSTX
Metrics endpoint: 0.0.0.0:9090
"#;

        let expected_str_v6 = r#"
Stacks node host: 127.0.0.1:20443
Signer endpoint: [::1]:30000
Stacks address: ST3FPN8KBZ3YPBP0ZJGAAHTVFMQDTJCR5QPS7VTNJ
Public key: 03bc489f27da3701d9f9e577c88de5567cf4023111b7577042d55cde4d823a3505
Network: testnet
Database path: :memory:
DKG transaction fee: 0.01 uSTX
Metrics endpoint: 0.0.0.0:9090
"#;

        assert!(
            config_str == expected_str_v4 || config_str == expected_str_v6,
            "Config string does not match expected output. Actual:\n{}",
            config_str
        );
    }

    #[test]
    // Test the same private key twice, with and without a compression flag.
    // Ensure that the address is the same in both cases.
    fn test_stacks_addr_from_priv_key() {
        // 64 bytes, no compression flag
        let sk_hex = "2de4e77aab89c0c2570bb8bb90824f5cf2a5204a975905fee450ff9dad0fcf28";

        let expected_addr = "SP1286C62P3TAWVQV2VM2CEGTRBQZSZ6MHMS9RW05";

        let config_toml = format!(
            r#"
stacks_private_key = "{sk_hex}"
node_host = "localhost"
endpoint = "localhost:30000"
network = "mainnet"
auth_password = "abcd"
db_path = ":memory:"
            "#
        );
        let config = GlobalConfig::load_from_str(&config_toml).unwrap();
        assert_eq!(config.stacks_address.to_string(), expected_addr);

        // 65 bytes (with compression flag)
        let sk_hex = "2de4e77aab89c0c2570bb8bb90824f5cf2a5204a975905fee450ff9dad0fcf2801";

        let config_toml = format!(
            r#"
stacks_private_key = "{sk_hex}"
node_host = "localhost"
endpoint = "localhost:30000"
network = "mainnet"
auth_password = "abcd"
db_path = ":memory:"
            "#
        );
        let config = GlobalConfig::load_from_str(&config_toml).unwrap();
        assert_eq!(config.stacks_address.to_string(), expected_addr);
    }
}
