// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2023 Stacks Open Internet Foundation
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

use std::collections::{HashMap, HashSet};
use std::{fmt, fs};

use clarity::vm::types::{
    QualifiedContractIdentifier, StacksAddressExtensions, StandardPrincipalData,
};
use rand::seq::SliceRandom;
use rand::{thread_rng, Rng, RngCore};
use rusqlite::types::ToSql;
use rusqlite::{params, Connection, OpenFlags, OptionalExtension, Row, Transaction};
use stacks_common::types::net::{PeerAddress, PeerHost};
use stacks_common::types::sqlite::NO_PARAMS;
use stacks_common::util;
use stacks_common::util::hash::{
    bin_bytes, hex_bytes, to_bin, to_hex, Hash160, Sha256Sum, Sha512Trunc256Sum,
};
use stacks_common::util::macros::is_big_endian;
use stacks_common::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use stacks_common::util::{get_epoch_time_secs, log};

use crate::burnchains::{PrivateKey, PublicKey};
use crate::chainstate::stacks::{StacksPrivateKey, StacksPublicKey};
use crate::core::NETWORK_P2P_PORT;
use crate::net::asn::ASEntry4;
use crate::net::{Neighbor, NeighborAddress, NeighborKey, ServiceFlags};
use crate::util_lib::db::{
    query_count, query_row, query_rows, sqlite_open, tx_begin_immediate, tx_busy_handler,
    u64_to_sql, DBConn, Error as db_error, FromColumn, FromRow,
};
use crate::util_lib::strings::UrlString;

pub const PEERDB_VERSION: &str = "3";

const NUM_SLOTS: usize = 8;

impl FromColumn<PeerAddress> for PeerAddress {
    fn from_column(row: &Row, column_name: &str) -> Result<PeerAddress, db_error> {
        let addrbytes_bin: String = row.get_unwrap(column_name);
        if addrbytes_bin.len() != 128 {
            error!("Unparsable peer address {}", addrbytes_bin);
            return Err(db_error::ParseError);
        }
        let addrbytes = bin_bytes(&addrbytes_bin).map_err(|_e| {
            error!("Unparseable peer address {}", addrbytes_bin);
            db_error::ParseError
        })?;

        if addrbytes.len() != 16 {
            error!("Peer address has {} bytes; expected 16", addrbytes.len());
            return Err(db_error::ParseError);
        }

        let mut addrbytes_buf = [0u8; 16];
        addrbytes_buf.copy_from_slice(&addrbytes[0..16]);

        Ok(PeerAddress(addrbytes_buf))
    }
}

impl FromRow<QualifiedContractIdentifier> for QualifiedContractIdentifier {
    fn from_row(row: &Row) -> Result<QualifiedContractIdentifier, db_error> {
        let cid_str: String = row.get_unwrap("smart_contract_id");
        let cid =
            QualifiedContractIdentifier::parse(&cid_str).map_err(|_e| db_error::ParseError)?;

        Ok(cid)
    }
}

#[derive(PartialEq, Clone)]
pub struct LocalPeer {
    pub network_id: u32,
    pub parent_network_id: u32,
    nonce: [u8; 32],
    pub private_key: Secp256k1PrivateKey,
    pub private_key_expire: u64,

    pub addrbytes: PeerAddress,
    pub port: u16,
    pub services: u16,
    pub data_url: UrlString,
    pub stacker_dbs: Vec<QualifiedContractIdentifier>,

    // filled in and curated at runtime
    pub public_ip_address: Option<(PeerAddress, u16)>,
}

impl fmt::Display for LocalPeer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "local.{:x}://(bind={:?})(pub={:?})",
            self.network_id,
            &self.addrbytes.to_socketaddr(self.port),
            &self
                .public_ip_address
                .map(|(ref addrbytes, ref port)| addrbytes.to_socketaddr(*port))
        )
    }
}

impl fmt::Debug for LocalPeer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "local.{:x}://(bind={:?})(pub={:?})",
            self.network_id,
            &self.addrbytes.to_socketaddr(self.port),
            &self
                .public_ip_address
                .map(|(ref addrbytes, ref port)| addrbytes.to_socketaddr(*port))
        )
    }
}

impl LocalPeer {
    pub fn new(
        network_id: u32,
        parent_network_id: u32,
        addrbytes: PeerAddress,
        port: u16,
        privkey: Option<Secp256k1PrivateKey>,
        key_expire: u64,
        data_url: UrlString,
        stacker_dbs: Vec<QualifiedContractIdentifier>,
    ) -> LocalPeer {
        let mut pkey = privkey.unwrap_or(Secp256k1PrivateKey::new());
        pkey.set_compress_public(true);

        let mut rng = thread_rng();
        let mut my_nonce = [0u8; 32];

        rng.fill_bytes(&mut my_nonce);

        let addr = addrbytes;
        let port = port;
        let services = (ServiceFlags::RELAY as u16)
            | (ServiceFlags::RPC as u16)
            | (ServiceFlags::STACKERDB as u16);

        info!(
            "Will be authenticating p2p messages with the following";
            "public key" => &Secp256k1PublicKey::from_private(&pkey).to_hex(),
            "services" => &to_hex(&services.to_be_bytes()),
            "Stacker DBs" => stacker_dbs.iter().map(|cid| format!("{}", &cid)).collect::<Vec<String>>().join(",")
        );

        LocalPeer {
            network_id,
            parent_network_id,
            nonce: my_nonce,
            private_key: pkey,
            private_key_expire: key_expire,
            addrbytes: addr,
            port,
            services,
            data_url,
            public_ip_address: None,
            stacker_dbs,
        }
    }

    pub fn to_neighbor_addr(&self) -> NeighborAddress {
        NeighborAddress {
            addrbytes: self.addrbytes.clone(),
            port: self.port,
            public_key_hash: Hash160::from_node_public_key(&StacksPublicKey::from_private(
                &self.private_key,
            )),
        }
    }

    /// Best-effort attempt to calculate a publicly-routable neighbor address for local peer
    pub fn to_public_neighbor_addr(&self) -> NeighborAddress {
        if let Some((peer_addr, peer_port)) = self.public_ip_address.as_ref() {
            NeighborAddress {
                addrbytes: peer_addr.clone(),
                port: *peer_port,
                public_key_hash: Hash160::from_node_public_key(&StacksPublicKey::from_private(
                    &self.private_key,
                )),
            }
        } else {
            self.to_neighbor_addr()
        }
    }
}

impl FromRow<LocalPeer> for LocalPeer {
    fn from_row(row: &Row) -> Result<LocalPeer, db_error> {
        let network_id: u32 = row.get_unwrap("network_id");
        let parent_network_id: u32 = row.get_unwrap("parent_network_id");
        let nonce_hex: String = row.get_unwrap("nonce");
        let privkey = Secp256k1PrivateKey::from_column(row, "private_key")?;
        let privkey_expire = u64::from_column(row, "private_key_expire")?;
        let addrbytes: PeerAddress = PeerAddress::from_column(row, "addrbytes")?;
        let port: u16 = row.get_unwrap("port");
        let services: u16 = row.get_unwrap("services");
        let data_url_str: String = row.get_unwrap("data_url");
        let stackerdbs_json: Option<String> = row.get_unwrap("stacker_dbs");

        let nonce_bytes = hex_bytes(&nonce_hex).map_err(|_e| {
            error!("Unparseable local peer nonce {}", &nonce_hex);
            db_error::ParseError
        })?;

        if nonce_bytes.len() != 32 {
            error!("Peer nonce has {} bytes: {}", nonce_bytes.len(), nonce_hex);
            return Err(db_error::ParseError);
        }

        let mut nonce_buf = [0u8; 32];
        nonce_buf.copy_from_slice(&nonce_bytes[0..32]);

        let data_url = UrlString::try_from(data_url_str).map_err(|_e| db_error::ParseError)?;
        let stacker_dbs: Vec<QualifiedContractIdentifier> =
            if let Some(stackerdbs_json) = stackerdbs_json {
                serde_json::from_str(&stackerdbs_json).map_err(|_| db_error::ParseError)?
            } else {
                vec![]
            };

        Ok(LocalPeer {
            network_id,
            parent_network_id,
            private_key: privkey,
            nonce: nonce_buf,
            private_key_expire: privkey_expire,
            addrbytes,
            port,
            services,
            data_url,
            public_ip_address: None,
            stacker_dbs,
        })
    }
}

impl FromRow<ASEntry4> for ASEntry4 {
    fn from_row(row: &Row) -> Result<ASEntry4, db_error> {
        let prefix: u32 = row.get_unwrap("prefix");
        let mask: u8 = row.get_unwrap("mask");
        let asn: u32 = row.get_unwrap("asn");
        let org: u32 = row.get_unwrap("org");

        Ok(ASEntry4 {
            prefix,
            mask,
            asn,
            org,
        })
    }
}

impl FromRow<Neighbor> for Neighbor {
    fn from_row(row: &Row) -> Result<Neighbor, db_error> {
        let peer_version: u32 = row.get_unwrap("peer_version");
        let network_id: u32 = row.get_unwrap("network_id");
        let addrbytes: PeerAddress = PeerAddress::from_column(row, "addrbytes")?;
        let port: u16 = row.get_unwrap("port");
        let mut public_key: Secp256k1PublicKey =
            Secp256k1PublicKey::from_column(row, "public_key")?;
        let expire_block_height = u64::from_column(row, "expire_block_height")?;
        let last_contact_time = u64::from_column(row, "last_contact_time")?;
        let asn: u32 = row.get_unwrap("asn");
        let org: u32 = row.get_unwrap("org");
        let allowed: i64 = row.get_unwrap("allowed");
        let denied: i64 = row.get_unwrap("denied");
        let in_degree: u32 = row.get_unwrap("in_degree");
        let out_degree: u32 = row.get_unwrap("out_degree");

        public_key.set_compressed(true);

        Ok(Neighbor {
            addr: NeighborKey {
                peer_version,
                network_id,
                addrbytes,
                port,
            },
            public_key,
            expire_block: expire_block_height,
            last_contact_time,
            asn,
            org,
            allowed,
            denied,
            in_degree,
            out_degree,
        })
    }
}

// In what is likely an abuse of Sqlite, the peer database is structured such that the `frontier`
// table stores peers keyed by a deterministically-chosen random "slot," instead of their IP/port.
// (i.e. the slot is determined by a cryptographic the hash of the IP/port).  The reason for this
// is to facilitate randomized peer eviction when the frontier table gets too big -- if a peer's
// possible slots are taken, then the _existing_ peer is pinged to see if it is still online.  If
// it is still online, the new peer will _not_ be inserted.  If it is offline, then it will be.
// This is done to ensure that the frontier represents live, long-lived peers to the greatest
// extent possible.

const PEERDB_INITIAL_SCHEMA: &[&str] = &[
    r#"
    CREATE TABLE frontier(
        peer_version INTEGER NOT NULL,
        network_id INTEGER NOT NULL,
        addrbytes TEXT NOT NULL,
        port INTEGER NOT NULL,
        public_key TEXT NOT NULL,
        expire_block_height INTEGER NOT NULL,
        last_contact_time INTEGER NOT NULL,
        asn INTEGER NOT NULL,
        org INTEGER NOT NULL,
        allowed INTEGER NOT NULL,
        denied INTEGER NOT NULL,
        initial INTEGER NOT NULL,   -- 1 if this was one of the initial neighbors, 0 otherwise
        in_degree INTEGER NOT NULL,
        out_degree INTEGER NOT NULL,

        -- used to deterministically insert and evict
        slot INTEGER UNIQUE NOT NULL,

        PRIMARY KEY(slot)
    );"#,
    r#"
    CREATE TABLE asn4(
        prefix INTEGER NOT NULL,
        mask INTEGER NOT NULL,

        asn INTEGER NOT NULL,
        org INTEGER,

        PRIMARY KEY(prefix,mask)
    );"#,
    "CREATE TABLE db_config(version TEXT NOT NULL);",
    r#"
    CREATE TABLE local_peer(
        network_id INT NOT NULL,
        parent_network_id INT NOT NULL,
        nonce TEXT NOT NULL,
        private_key TEXT NOT NULL,
        private_key_expire INTEGER NOT NULL,
        addrbytes TEXT NOT NULL,
        port INTEGER NOT NULL,
        services INTEGER NOT NULL,
        data_url TEXT NOT NULL
    );"#,
    r#"
    CREATE TABLE allowed_prefixes(
        prefix TEXT NOT NULL,
        mask INTEGER NOT NULL
    );"#,
    r#"
    CREATE TABLE denied_prefixes(
        prefix TEXT NOT NULL,
        mask INTEGER NOT NULL
    );"#,
];

const PEERDB_INDEXES: &[&str] =
    &["CREATE INDEX IF NOT EXISTS peer_address_index ON frontier(network_id,addrbytes,port);"];

const PEERDB_SCHEMA_2: &[&str] = &[
    r#"PRAGMA foreign_keys = ON;"#,
    r#"
    CREATE TABLE stackerdb_peers(
        smart_contract_id TEXT NOT NULL,
        peer_slot INTEGER NOT NULL,
        PRIMARY KEY(smart_contract_id,peer_slot),
        FOREIGN KEY(peer_slot) REFERENCES frontier(slot) ON DELETE CASCADE
    );
    "#,
    r#"
    CREATE INDEX IF NOT EXISTS index_stackedb_peers_by_contract ON stackerdb_peers(smart_contract_id);
    "#,
    r#"
    CREATE INDEX IF NOT EXISTS index_stackedb_peers_by_slot ON stackerdb_peers(peer_slot);
    "#,
    r#"
    ALTER TABLE local_peer ADD COLUMN stacker_dbs TEXT;
    "#,
    r#"
    UPDATE db_config SET version = 2;
    "#,
];

const PEERDB_SCHEMA_3: &[&str] = &[
    r#"
    ALTER TABLE frontier ADD COLUMN public BOOL NOT NULL DEFAULT 0;
    "#,
    "UPDATE db_config SET version = 3;",
];

#[derive(Debug)]
pub struct PeerDB {
    pub conn: Connection,
    pub readwrite: bool,
}

impl PeerDB {
    fn instantiate(
        &mut self,
        network_id: u32,
        parent_network_id: u32,
        privkey_opt: Option<Secp256k1PrivateKey>,
        key_expires: u64,
        data_url: UrlString,
        p2p_addr: PeerAddress,
        p2p_port: u16,
        asn4_entries: &[ASEntry4],
        initial_neighbors: &[Neighbor],
        stacker_dbs: &[QualifiedContractIdentifier],
    ) -> Result<(), db_error> {
        let localpeer = LocalPeer::new(
            network_id,
            parent_network_id,
            p2p_addr,
            p2p_port,
            privkey_opt,
            key_expires,
            data_url,
            vec![],
        );

        let tx = self.tx_begin()?;

        for row_text in PEERDB_INITIAL_SCHEMA {
            tx.execute_batch(row_text).map_err(db_error::SqliteError)?;
        }

        tx.execute(
            "INSERT INTO db_config (version) VALUES (?1)",
            &[&"1".to_string()],
        )
        .map_err(db_error::SqliteError)?;

        PeerDB::apply_schema_migrations(&tx)?;

        let local_peer_args = params![
            network_id,
            parent_network_id,
            to_hex(&localpeer.nonce),
            to_hex(&localpeer.private_key.to_bytes()),
            u64_to_sql(key_expires)?,
            to_bin(localpeer.addrbytes.as_bytes()),
            localpeer.port,
            localpeer.services,
            localpeer.data_url.as_str(),
            serde_json::to_string(stacker_dbs)
                .expect("FATAL: failed to serialize stacker db contract addresses"),
        ];

        tx.execute("INSERT INTO local_peer (network_id, parent_network_id, nonce, private_key, private_key_expire, addrbytes, port, services, data_url, stacker_dbs) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)", local_peer_args)
            .map_err(db_error::SqliteError)?;

        for neighbor in initial_neighbors.iter() {
            // since this is a neighbor the node operator is declaring exists, we treat it as
            // freshly-contacted.
            let mut neighbor = neighbor.clone();
            neighbor.last_contact_time = get_epoch_time_secs();

            // do we have this neighbor already?
            test_debug!("Add initial neighbor {:?}", &neighbor);
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &[])?;
            if !res {
                warn!("Failed to insert neighbor {:?}", &neighbor);
            }
        }

        for asn4 in asn4_entries {
            PeerDB::asn4_insert(&tx, &asn4)?;
        }

        for neighbor in initial_neighbors {
            PeerDB::set_initial_peer(
                &tx,
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port,
            )?;
        }

        tx.commit().map_err(db_error::SqliteError)?;

        self.add_indexes()?;
        Ok(())
    }

    fn add_indexes(&mut self) -> Result<(), db_error> {
        debug!("Add indexes to peer DB");
        let tx = self.tx_begin()?;
        for row_text in PEERDB_INDEXES {
            tx.execute_batch(row_text).map_err(db_error::SqliteError)?;
        }
        tx.commit()?;
        Ok(())
    }

    fn get_schema_version(conn: &Connection) -> Result<String, db_error> {
        let version = conn
            .query_row("SELECT MAX(version) from db_config", NO_PARAMS, |row| {
                row.get(0)
            })
            .optional()?
            .unwrap_or("1".to_string());
        Ok(version)
    }

    /// Tag each address in the peer DB as public if its address is not private.
    /// Happens as part of the schema 3 migration
    fn update_peerdb_public_addrs(tx: &Transaction) -> Result<(), db_error> {
        let all_peers = Self::get_all_peers(tx)?;
        for peer in all_peers {
            let public = !peer.addr.addrbytes.is_in_private_range();
            debug!("Marking peer {:?} as public? {}", &peer, public);
            Self::update_peer(tx, &peer)?;
        }
        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn apply_schema_2(tx: &Transaction) -> Result<(), db_error> {
        test_debug!("Apply schema 2 to peer DB");
        for row_text in PEERDB_SCHEMA_2 {
            tx.execute_batch(row_text).map_err(db_error::SqliteError)?;
        }
        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn apply_schema_3(tx: &Transaction) -> Result<(), db_error> {
        test_debug!("Apply schema 3 to peer DB");
        for row_text in PEERDB_SCHEMA_3 {
            tx.execute_batch(row_text).map_err(db_error::SqliteError)?;
        }
        Self::update_peerdb_public_addrs(tx)?;
        Ok(())
    }

    fn apply_schema_migrations(tx: &Transaction) -> Result<String, db_error> {
        test_debug!("Apply any schema migrations");
        let expected_version = PEERDB_VERSION.to_string();
        let mut ret = None;
        loop {
            match PeerDB::get_schema_version(tx) {
                Ok(version) => {
                    if ret.is_none() {
                        ret = Some(version.clone());
                    }
                    if version == "1" {
                        PeerDB::apply_schema_2(tx)?;
                    } else if version == "2" {
                        PeerDB::apply_schema_3(tx)?;
                    } else if version == expected_version {
                        return Ok(ret.expect("unreachable"));
                    } else {
                        panic!("The schema version of the peer DB is invalid.")
                    }
                }
                Err(e) => panic!("Error obtaining the version of the peer DB: {:?}", e),
            }
        }
    }

    pub fn update_local_peer(
        &mut self,
        network_id: u32,
        parent_network_id: u32,
        data_url: UrlString,
        p2p_port: u16,
        stacker_dbs: &[QualifiedContractIdentifier],
    ) -> Result<(), db_error> {
        let local_peer_args = params![
            p2p_port,
            data_url.as_str(),
            serde_json::to_string(stacker_dbs)
                .expect("FATAL: unable to serialize Vec<QualifiedContractIdentifier>"),
            network_id,
            parent_network_id,
        ];

        match self.conn.execute("UPDATE local_peer SET port = ?1, data_url = ?2, stacker_dbs = ?3 WHERE network_id = ?4 AND parent_network_id = ?5",
                                local_peer_args) {
            Ok(_) => Ok(()),
            Err(e) => Err(db_error::SqliteError(e))
        }
    }

    fn reset_denies(tx: &Transaction) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET denied = 0", NO_PARAMS)
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    fn reset_allows(tx: &Transaction) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET allowed = 0", NO_PARAMS)
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    fn refresh_denies(tx: &Transaction) -> Result<(), db_error> {
        PeerDB::reset_denies(tx)?;
        let deny_cidrs = PeerDB::get_denied_cidrs(tx)?;
        for (prefix, mask) in deny_cidrs.into_iter() {
            debug!("Refresh deny {}/{}", &prefix, mask);
            PeerDB::apply_cidr_filter(tx, &prefix, mask, "denied", i64::MAX)?;
        }
        Ok(())
    }

    fn refresh_allows(tx: &Transaction) -> Result<(), db_error> {
        PeerDB::reset_allows(tx)?;
        let allow_cidrs = PeerDB::get_allowed_cidrs(tx)?;
        for (prefix, mask) in allow_cidrs.into_iter() {
            debug!("Refresh allow {}/{}", &prefix, mask);
            PeerDB::apply_cidr_filter(tx, &prefix, mask, "allowed", i64::MAX)?;
        }
        Ok(())
    }

    /// Open the burn database at the given path.  Open read-only or read/write.
    /// If opened for read/write and it doesn't exist, instantiate it.
    pub fn connect(
        path: &String,
        readwrite: bool,
        network_id: u32,
        parent_network_id: u32,
        privkey_opt: Option<Secp256k1PrivateKey>,
        key_expires: u64,
        p2p_addr: PeerAddress,
        p2p_port: u16,
        data_url: UrlString,
        asn4_recs: &[ASEntry4],
        initial_neighbors: Option<&[Neighbor]>,
        stacker_dbs: &[QualifiedContractIdentifier],
    ) -> Result<PeerDB, db_error> {
        let mut create_flag = false;
        let open_flags = if fs::metadata(path).is_err() {
            // need to create
            if readwrite {
                create_flag = true;
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
            } else {
                return Err(db_error::NoDBError);
            }
        } else {
            // can just open
            // NOTE: we may need to apply some migrations, so always open read-write at this point.
            OpenFlags::SQLITE_OPEN_READ_WRITE
        };

        let conn = sqlite_open(path, open_flags, false)?;

        let mut db = PeerDB { conn, readwrite };

        if create_flag {
            // instantiate!
            match initial_neighbors {
                Some(ref neighbors) => {
                    db.instantiate(
                        network_id,
                        parent_network_id,
                        privkey_opt,
                        key_expires,
                        data_url,
                        p2p_addr,
                        p2p_port,
                        asn4_recs,
                        neighbors,
                        stacker_dbs,
                    )?;
                }
                None => {
                    db.instantiate(
                        network_id,
                        parent_network_id,
                        privkey_opt,
                        key_expires,
                        data_url,
                        p2p_addr,
                        p2p_port,
                        asn4_recs,
                        &[],
                        stacker_dbs,
                    )?;
                }
            }
        } else {
            let peerdb_version = PeerDB::get_schema_version(&db.conn)?;
            if peerdb_version != PEERDB_VERSION {
                let tx = db.tx_begin()?;
                PeerDB::apply_schema_migrations(&tx)?;
                tx.commit()?;
            }

            db.update_local_peer(
                network_id,
                parent_network_id,
                data_url,
                p2p_port,
                stacker_dbs,
            )?;

            let tx = db.tx_begin()?;
            PeerDB::refresh_allows(&tx)?;
            PeerDB::refresh_denies(&tx)?;
            PeerDB::clear_initial_peers(&tx)?;
            if let Some(privkey) = privkey_opt {
                PeerDB::set_local_private_key(&tx, &privkey, key_expires)?;
            }

            if let Some(neighbors) = initial_neighbors {
                for neighbor in neighbors {
                    PeerDB::set_initial_peer(
                        &tx,
                        neighbor.addr.network_id,
                        &neighbor.addr.addrbytes,
                        neighbor.addr.port,
                    )?;
                }
            }

            tx.commit()?;
        }
        debug!("Opened PeerDB {} readwrite={}", &path, readwrite);

        // *now* instantiate the DB with the appropriate sql flags
        let open_flags = if readwrite {
            OpenFlags::SQLITE_OPEN_READ_WRITE
        } else {
            OpenFlags::SQLITE_OPEN_READ_ONLY
        };

        let conn = sqlite_open(path, open_flags, true)?;

        let db = PeerDB { conn, readwrite };
        Ok(db)
    }

    /// Open an existing peer DB
    pub fn open(path: &str, readwrite: bool) -> Result<PeerDB, db_error> {
        if fs::metadata(path).is_err() {
            return Err(db_error::NoDBError);
        }

        let open_flags = if readwrite {
            OpenFlags::SQLITE_OPEN_READ_WRITE
        } else {
            OpenFlags::SQLITE_OPEN_READ_ONLY
        };
        let conn = sqlite_open(path, open_flags, true)?;

        let db = PeerDB { conn, readwrite };

        Ok(db)
    }

    /// Open a peer database in memory (used for testing)
    #[cfg(any(test, feature = "testing"))]
    pub fn connect_memory(
        network_id: u32,
        parent_network_id: u32,
        key_expires: u64,
        data_url: UrlString,
        asn4_entries: &[ASEntry4],
        initial_neighbors: &[Neighbor],
    ) -> Result<PeerDB, db_error> {
        let conn = Connection::open_in_memory().map_err(db_error::SqliteError)?;

        let mut db = PeerDB {
            conn,
            readwrite: true,
        };

        db.instantiate(
            network_id,
            parent_network_id,
            None,
            key_expires,
            data_url,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            NETWORK_P2P_PORT,
            asn4_entries,
            initial_neighbors,
            &[],
        )?;

        let tx = db.tx_begin()?;
        PeerDB::apply_schema_migrations(&tx)?;
        tx.commit()?;
        Ok(db)
    }

    pub fn conn(&self) -> &Connection {
        &self.conn
    }

    pub fn tx_begin(&mut self) -> Result<Transaction<'_>, db_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly);
        }

        let tx = tx_begin_immediate(&mut self.conn)?;
        Ok(tx)
    }

    /// Read the local peer record
    pub fn get_local_peer(conn: &DBConn) -> Result<LocalPeer, db_error> {
        let qry = "SELECT * FROM local_peer LIMIT 1".to_string();
        let rows = query_rows::<LocalPeer, _>(conn, &qry, NO_PARAMS)?;

        match rows.len() {
            1 => Ok(rows[0].clone()),
            _ => {
                // only one item here
                panic!("Got multiple LocalPeer rows, or 0");
            }
        }
    }

    /// Set the local IP address and port
    pub fn set_local_ipaddr(
        tx: &Transaction,
        addrbytes: &PeerAddress,
        port: u16,
    ) -> Result<(), db_error> {
        tx.execute(
            "UPDATE local_peer SET addrbytes = ?1, port = ?2",
            params![to_bin(addrbytes.as_bytes()), port], // TODO: double check if delete as_ref here
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Set local service availability
    pub fn set_local_services(tx: &Transaction, services: u16) -> Result<(), db_error> {
        tx.execute("UPDATE local_peer SET services = ?1", params![services])
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Set local private key and expiry
    pub fn set_local_private_key(
        tx: &Transaction,
        privkey: &Secp256k1PrivateKey,
        expire_block: u64,
    ) -> Result<(), db_error> {
        let args = params![to_hex(&privkey.to_bytes()), u64_to_sql(expire_block)?];
        tx.execute(
            "UPDATE local_peer SET private_key = ?1, private_key_expire = ?2",
            args,
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Re-key and return the new local peer
    pub fn rekey(&mut self, new_expire_block: u64) -> Result<LocalPeer, db_error> {
        if new_expire_block > (1 << 63) - 1 {
            return Err(db_error::Overflow);
        }

        let new_key = Secp256k1PrivateKey::new();
        {
            let tx = self.tx_begin()?;

            PeerDB::set_local_private_key(&tx, &new_key, new_expire_block)?;
            tx.commit().map_err(db_error::SqliteError)?;
        }

        PeerDB::get_local_peer(self.conn())
    }

    /// Calculate the "slots" in the peer database where this peer can be inserted.
    /// Slots are distributed uniformly at random between 0 and 2**24.
    /// NUM_SLOTS will be returned.
    pub fn peer_slots(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<Vec<u32>, db_error> {
        let local_peer = PeerDB::get_local_peer(conn)?;
        let mut ret = vec![];
        for i in 0..NUM_SLOTS {
            // pack peer address, port, and index.
            // Randomize with local nonce
            let mut bytes = vec![];
            bytes.extend_from_slice(&local_peer.nonce);
            bytes.push(i as u8);
            bytes.extend_from_slice(peer_addr.as_bytes());

            bytes.push((peer_port & 0xff) as u8);
            bytes.push((peer_port >> 8) as u8);

            bytes.push(((network_id & 0xff000000) >> 24) as u8);
            bytes.push(((network_id & 0x00ff0000) >> 16) as u8);
            bytes.push(((network_id & 0x0000ff00) >> 8) as u8);
            bytes.push((network_id & 0x000000ff) as u8);

            let h = Sha512Trunc256Sum::from_data(&bytes[..]);
            let slot: u32 = (h.as_bytes()[0] as u32)
                | ((h.as_bytes()[1] as u32) << 8)
                | ((h.as_bytes()[2] as u32) << 16);

            ret.push(slot);
        }
        Ok(ret)
    }

    /// Group a list of peers by public key, and return the one with the highest last-contact time
    fn query_peers(
        conn: &Connection,
        qry: &str,
        args: &[&dyn ToSql],
    ) -> Result<Vec<Neighbor>, db_error> {
        let peers: Vec<Neighbor> = query_rows(conn, qry, args)?;
        let mut grouped_by_public_key: HashMap<Secp256k1PublicKey, Neighbor> = HashMap::new();
        for peer in peers.into_iter() {
            if let Some(cur_peer) = grouped_by_public_key.get_mut(&peer.public_key) {
                if cur_peer.last_contact_time < peer.last_contact_time {
                    *cur_peer = peer;
                }
            } else {
                grouped_by_public_key.insert(peer.public_key.clone(), peer);
            }
        }
        Ok(grouped_by_public_key.into_values().collect())
    }

    /// Query a single peer.
    /// If multiple rows are returned, then only the first-found row is reported.
    fn query_peer(
        conn: &Connection,
        qry: &str,
        args: &[&dyn ToSql],
    ) -> Result<Option<Neighbor>, db_error> {
        let mut peers = Self::query_peers(conn, qry, args)?;
        Ok(peers.pop())
    }

    /// Get a peer from the DB.
    pub fn get_peer(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<Option<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3";
        let args = params![network_id, peer_addr.to_bin(), peer_port,];
        Self::query_peer(conn, qry, args)
    }

    pub fn has_peer(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        let qry = "SELECT 1 FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3";
        let args = params![network_id, peer_addr.to_bin(), peer_port];
        Ok(query_row::<i64, _>(conn, &qry, args)?
            .map(|x| x == 1)
            .unwrap_or(false))
    }

    /// Get peer by port (used in tests where the IP address doesn't really matter)
    #[cfg(any(test, feature = "testing"))]
    pub fn get_peer_by_port(
        conn: &DBConn,
        network_id: u32,
        peer_port: u16,
    ) -> Result<Option<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier WHERE network_id = ?1 AND port = ?2";
        let args = params![network_id, peer_port];
        Self::query_peer(conn, qry, args)
    }

    /// Get a peer record at a particular slot
    pub fn get_peer_at(
        conn: &DBConn,
        network_id: u32,
        slot: u32,
    ) -> Result<Option<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier WHERE network_id = ?1 AND slot = ?2";
        let args = params![network_id, slot];

        // N.B. we don't use Self::query_peer() here because `slot` is the primary key
        query_row::<Neighbor, _>(conn, &qry, args)
    }

    /// Is there any peer at a particular slot?
    pub fn has_peer_at(conn: &DBConn, network_id: u32, slot: u32) -> Result<bool, db_error> {
        let qry = "SELECT 1 FROM frontier WHERE network_id = ?1 AND slot = ?2";
        let args = params![network_id, slot];
        Ok(query_row::<i64, _>(conn, &qry, args)?
            .map(|x| x == 1)
            .unwrap_or(false))
    }

    /// Is a peer denied?
    pub fn is_peer_denied(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        match PeerDB::get_peer(conn, network_id, peer_addr, peer_port)? {
            Some(neighbor) => {
                if neighbor.is_denied() {
                    return Ok(true);
                }
                if PeerDB::is_address_denied(conn, &neighbor.addr.addrbytes)? {
                    return Ok(true);
                }
                return Ok(false);
            }
            None => {
                if PeerDB::is_address_denied(conn, &peer_addr)? {
                    return Ok(true);
                }
                return Ok(false);
            }
        }
    }

    /// Is a peer always allowed?
    pub fn is_peer_always_allowed(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        match PeerDB::get_peer(conn, network_id, peer_addr, peer_port)? {
            Some(neighbor) => {
                if neighbor.allowed < 0 {
                    return Ok(true);
                }
                return Ok(false);
            }
            None => {
                return Ok(false);
            }
        }
    }

    /// Get all always-allowed peers
    pub fn get_always_allowed_peers(
        conn: &DBConn,
        network_id: u32,
    ) -> Result<Vec<Neighbor>, db_error> {
        let local_peer = Self::get_local_peer(conn)?;
        let sql = "SELECT * FROM frontier WHERE allowed < 0 AND network_id = ?1 ORDER BY RANDOM()";
        let allow_rows: Vec<Neighbor> = Self::query_peers(conn, sql, params![&network_id])?;
        Ok(allow_rows
            .into_iter()
            .filter(|neighbor| {
                // omit local peer if it ever gets entered by mistake, since we can't talk to
                // ourselves.
                neighbor.public_key.to_bytes_compressed()
                    != StacksPublicKey::from_private(&local_peer.private_key).to_bytes_compressed()
            })
            .collect())
    }

    /// Get the bootstrap peers
    pub fn get_bootstrap_peers(conn: &DBConn, network_id: u32) -> Result<Vec<Neighbor>, db_error> {
        let sql = "SELECT * FROM frontier WHERE initial = 1 AND network_id = ?1 ORDER BY RANDOM()";
        let allow_rows = Self::query_peers(conn, sql, params![&network_id])?;
        Ok(allow_rows)
    }

    /// Insert or replace stacker DB contract IDs for a peer, given its slot
    pub fn insert_or_replace_stacker_dbs(
        tx: &Transaction,
        slot: u32,
        smart_contracts: &[QualifiedContractIdentifier],
    ) -> Result<(), db_error> {
        for cid in smart_contracts {
            test_debug!("Add Stacker DB contract to slot {}: {}", slot, cid);
            let args = params![cid.to_string(), slot];
            tx.execute("INSERT OR REPLACE INTO stackerdb_peers (smart_contract_id,peer_slot) VALUES (?1,?2)", args)
                .map_err(db_error::SqliteError)?;
        }
        Ok(())
    }

    /// Drop all stacker DB contract IDs for a peer, given its slot
    pub fn drop_stacker_dbs(tx: &Transaction, slot: u32) -> Result<(), db_error> {
        tx.execute("DELETE FROM stackerdb_peers WHERE peer_slot = ?1", &[&slot])
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Insert or replace a neighbor into a given slot
    pub fn insert_or_replace_peer(
        tx: &Transaction,
        neighbor: &Neighbor,
        slot: u32,
    ) -> Result<(), db_error> {
        let old_peer_opt = PeerDB::get_peer_at(tx, neighbor.addr.network_id, slot)?;

        let neighbor_args = params![
            neighbor.addr.peer_version,
            neighbor.addr.network_id,
            to_bin(neighbor.addr.addrbytes.as_bytes()),
            neighbor.addr.port,
            to_hex(&neighbor.public_key.to_bytes_compressed()),
            u64_to_sql(neighbor.expire_block)?,
            u64_to_sql(neighbor.last_contact_time)?,
            neighbor.asn,
            neighbor.org,
            neighbor.allowed,
            neighbor.denied,
            neighbor.in_degree,
            neighbor.out_degree,
            0i64,
            slot,
            !neighbor.addr.addrbytes.is_in_private_range()
        ];

        tx.execute("INSERT OR REPLACE INTO frontier (peer_version, network_id, addrbytes, port, public_key, expire_block_height, last_contact_time, asn, org, allowed, denied, in_degree, out_degree, initial, slot, public) \
                   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16)", neighbor_args)
            .map_err(db_error::SqliteError)?;

        if let Some(old_peer) = old_peer_opt {
            if old_peer.addr != neighbor.addr
                || old_peer.public_key.to_bytes_compressed()
                    != neighbor.public_key.to_bytes_compressed()
            {
                // the peer for this slot changed. Drop the associated stacker DB records
                debug!("Peer at slot {} changed; dropping its DBs", slot);
                PeerDB::drop_stacker_dbs(tx, slot)?;
            }
        }

        Ok(())
    }

    /// Remove a peer from the peer database, as well as its stacker DB contracts
    pub fn drop_peer(
        tx: &Transaction,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<(), db_error> {
        let slot_opt = Self::find_peer_slot(tx, network_id, peer_addr, peer_port)?;
        tx.execute(
            "DELETE FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3",
            params![network_id, peer_addr.to_bin(), peer_port,],
        )
        .map_err(db_error::SqliteError)?;

        if let Some(slot) = slot_opt {
            Self::drop_stacker_dbs(tx, slot)?;
        }
        Ok(())
    }

    /// Is a peer one of this node's initial neighbors?
    /// Only checks IP address.
    pub fn is_initial_peer(
        conn: &DBConn,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<bool, db_error> {
        let res: Option<i64> = query_row(
            conn,
            "SELECT initial FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3 ORDER BY last_contact_time DESC LIMIT 1",
            params![network_id, peer_addr.to_bin(), peer_port],
        )?;

        match res {
            Some(x) => Ok(x != 0),
            None => Ok(false),
        }
    }

    /// Set a peer as an initial peer.
    /// Does so for all rows with the given IP address.
    pub fn set_initial_peer(
        tx: &Transaction,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
    ) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET initial = 1 WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3",
                    params![network_id, peer_addr.to_bin(), peer_port])
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// clear all initial peers
    fn clear_initial_peers(tx: &Transaction) -> Result<(), db_error> {
        tx.execute("UPDATE frontier SET initial = 0", NO_PARAMS)
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Set/unset allow flag for a peer
    /// Pass -1 for "always"
    pub fn set_allow_peer(
        tx: &Transaction,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
        allow_deadline: i64,
    ) -> Result<(), db_error> {
        let num_updated = tx.execute("UPDATE frontier SET allowed = ?1 WHERE network_id = ?2 AND addrbytes = ?3 AND port = ?4",
                   params![allow_deadline, network_id, peer_addr.to_bin(), peer_port])
            .map_err(db_error::SqliteError)?;

        if num_updated == 0 {
            // we're preemptively allowing
            let nk = NeighborKey {
                peer_version: 0,
                network_id,
                addrbytes: peer_addr.clone(),
                port: peer_port,
            };
            let empty_key = StacksPublicKey::from_private(&StacksPrivateKey::new());
            let mut empty_neighbor = Neighbor::empty(&nk, &empty_key, 0);

            empty_neighbor.allowed = allow_deadline;

            debug!("Preemptively allow peer {:?}", &nk);
            if !PeerDB::try_insert_peer(tx, &empty_neighbor, &[])? {
                let mut slots = PeerDB::peer_slots(tx, network_id, peer_addr, peer_port)?;
                let slot = slots.pop().expect("BUG: no slots");
                warn!(
                    "Forcing replacement of peer at slot {} for allowed peer {:?}",
                    slot, &empty_neighbor.addr
                );
                PeerDB::insert_or_replace_peer(tx, &empty_neighbor, slot)?;
            }
        }

        Ok(())
    }

    /// Set/unset deny flag for a peer
    /// negative values aren't allowed
    pub fn set_deny_peer(
        tx: &Transaction,
        network_id: u32,
        peer_addr: &PeerAddress,
        peer_port: u16,
        deny_deadline: u64,
    ) -> Result<(), db_error> {
        let args = params![
            u64_to_sql(deny_deadline)?,
            network_id,
            peer_addr.to_bin(),
            peer_port,
        ];
        let num_updated = tx.execute("UPDATE frontier SET denied = ?1 WHERE network_id = ?2 AND addrbytes = ?3 AND port = ?4", args)
            .map_err(db_error::SqliteError)?;

        if num_updated == 0 {
            // we're preemptively denying
            let nk = NeighborKey {
                peer_version: 0,
                network_id,
                addrbytes: peer_addr.clone(),
                port: peer_port,
            };
            let empty_key = StacksPublicKey::from_private(&StacksPrivateKey::new());
            let mut empty_neighbor = Neighbor::empty(&nk, &empty_key, 0);

            empty_neighbor.denied = deny_deadline as i64;

            debug!("Preemptively deny peer {:?}", &nk);
            if !PeerDB::try_insert_peer(tx, &empty_neighbor, &[])? {
                let mut slots = PeerDB::peer_slots(tx, network_id, peer_addr, peer_port)?;
                let slot = slots.pop().expect("BUG: no slots");
                warn!(
                    "Forcing replacement of peer at slot {} for denied peer {:?}",
                    slot, &empty_neighbor.addr
                );
                PeerDB::insert_or_replace_peer(tx, &empty_neighbor, slot)?;
            }
        }

        Ok(())
    }

    /// Update an existing peer's entries.  Does nothing if the peer is not present.
    pub fn update_peer(tx: &Transaction, neighbor: &Neighbor) -> Result<(), db_error> {
        let old_peer_opt = PeerDB::get_peer(
            tx,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )?;

        let args = params![
            neighbor.addr.peer_version,
            to_hex(&neighbor.public_key.to_bytes_compressed()),
            u64_to_sql(neighbor.expire_block)?,
            u64_to_sql(neighbor.last_contact_time)?,
            neighbor.asn,
            neighbor.org,
            neighbor.allowed,
            neighbor.denied,
            neighbor.in_degree,
            neighbor.out_degree,
            !neighbor.addr.addrbytes.is_in_private_range(),
            neighbor.addr.network_id,
            to_bin(neighbor.addr.addrbytes.as_bytes()),
            neighbor.addr.port,
        ];

        tx.execute("UPDATE frontier SET peer_version = ?1, public_key = ?2, expire_block_height = ?3, last_contact_time = ?4, asn = ?5, org = ?6, allowed = ?7, denied = ?8, in_degree = ?9, out_degree = ?10, public = ?11 \
                    WHERE network_id = ?12 AND addrbytes = ?13 AND port = ?14", args)
            .map_err(db_error::SqliteError)?;

        if let Some(old_peer) = old_peer_opt {
            let slot_opt = Self::find_peer_slot(
                tx,
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port,
            )?;
            if old_peer.public_key.to_bytes_compressed()
                != neighbor.public_key.to_bytes_compressed()
            {
                // this peer has re-keyed, so it might be a new peer altogether.
                // require it to re-announce its DBs
                if let Some(slot) = slot_opt {
                    debug!("Peer at slot {} changed; dropping its DBs", slot);
                    PeerDB::drop_stacker_dbs(tx, slot)?;
                }
            }
        }
        Ok(())
    }

    /// Find a peer's slot in the DB.
    /// Return Some(slot id) if the peer is inserted
    /// Return None if not.
    fn find_peer_slot(
        conn: &Connection,
        network_id: u32,
        addrbytes: &PeerAddress,
        port: u16,
    ) -> Result<Option<u32>, db_error> {
        let qry =
            "SELECT slot FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3";
        let args = params![network_id, addrbytes.to_bin(), port];
        Ok(query_row::<u32, _>(conn, qry, args)?)
    }

    /// Get the list of stacker DB contract IDs for a given set of slots.
    /// The list will contain distinct contract IDs.
    fn get_stacker_dbs_by_slot(
        conn: &Connection,
        used_slot: u32,
    ) -> Result<Vec<QualifiedContractIdentifier>, db_error> {
        let mut db_set = HashSet::new();
        let qry = "SELECT smart_contract_id FROM stackerdb_peers WHERE peer_slot = ?1";
        let dbs = query_rows(conn, qry, &[&used_slot])?;
        for cid in dbs.into_iter() {
            db_set.insert(cid);
        }

        Ok(db_set.into_iter().collect())
    }

    /// Get the slots for all peers that replicate a particular stacker DB
    fn get_stacker_db_slots(
        conn: &Connection,
        smart_contract: &QualifiedContractIdentifier,
    ) -> Result<Vec<u32>, db_error> {
        let qry = "SELECT peer_slot FROM stackerdb_peers WHERE smart_contract_id = ?1";
        let args = params![smart_contract.to_string()];
        query_rows(conn, qry, args)
    }

    /// Get a peer's advertized stacker DBs
    pub fn static_get_peer_stacker_dbs(
        conn: &Connection,
        neighbor: &Neighbor,
    ) -> Result<Vec<QualifiedContractIdentifier>, db_error> {
        let used_slot_opt = PeerDB::find_peer_slot(
            conn,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )?;
        if let Some(used_slot) = used_slot_opt {
            Self::get_stacker_dbs_by_slot(conn, used_slot)
        } else {
            Ok(vec![])
        }
    }

    /// Get a peer's advertized stacker DBs by their IDs.
    pub fn get_peer_stacker_dbs(
        &self,
        neighbor: &Neighbor,
    ) -> Result<Vec<QualifiedContractIdentifier>, db_error> {
        PeerDB::static_get_peer_stacker_dbs(&self.conn, neighbor)
    }

    /// Update an existing peer's stacker DB IDs.
    /// Calculates the delta between what's in the DB now, and what's in `dbs`, and deletes the
    /// records absent from `dbs` and adds records not present in the DB.
    /// Does nothing if the peer is not present.
    pub fn update_peer_stacker_dbs(
        tx: &Transaction,
        neighbor: &Neighbor,
        dbs: &[QualifiedContractIdentifier],
    ) -> Result<(), db_error> {
        let slot = if let Some(slot) = PeerDB::find_peer_slot(
            tx,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )? {
            slot
        } else {
            return Ok(());
        };
        let cur_dbs_set: HashSet<_> = PeerDB::static_get_peer_stacker_dbs(tx, neighbor)?
            .into_iter()
            .collect();
        let new_dbs_set: HashSet<QualifiedContractIdentifier> =
            dbs.iter().map(|cid| cid.clone()).collect();
        let to_insert: Vec<_> = new_dbs_set.difference(&cur_dbs_set).collect();
        let to_delete: Vec<_> = cur_dbs_set.difference(&new_dbs_set).collect();

        let sql = "DELETE FROM stackerdb_peers WHERE smart_contract_id = ?1 AND peer_slot = ?2";
        for cid in to_delete.into_iter() {
            test_debug!("Delete Stacker DB for {:?}: {}", &neighbor.addr, &cid);
            let args = params![cid.to_string(), slot];
            tx.execute(sql, args).map_err(db_error::SqliteError)?;
        }

        let sql =
            "INSERT OR REPLACE INTO stackerdb_peers (smart_contract_id,peer_slot) VALUES (?1,?2)";
        for cid in to_insert.iter() {
            test_debug!("Add Stacker DB for {:?}: {}", &neighbor.addr, &cid);
            let args = params![cid.to_string(), slot];
            tx.execute(sql, args).map_err(db_error::SqliteError)?;
        }

        Ok(())
    }

    /// Try to insert a peer at one of its slots.
    /// Does not insert the peer if it is already present, but will instead try to update it with
    /// this peer's information.
    /// If at least one slot was empty, or if the peer is already present and can be updated, then insert/update the peer and return true.
    /// If all slots are occupied, return false.
    pub fn try_insert_peer(
        tx: &Transaction,
        neighbor: &Neighbor,
        stacker_dbs: &[QualifiedContractIdentifier],
    ) -> Result<bool, db_error> {
        let present = PeerDB::has_peer(
            tx,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )?;
        if present {
            // already here
            PeerDB::update_peer(tx, neighbor)?;
            PeerDB::update_peer_stacker_dbs(tx, neighbor, stacker_dbs)?;
            return Ok(true);
        }

        let slots = PeerDB::peer_slots(
            tx,
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )?;
        for slot in slots.iter() {
            let used_slot = PeerDB::has_peer_at(tx, neighbor.addr.network_id, *slot)?;
            if !used_slot {
                // have a spare slot!
                PeerDB::insert_or_replace_peer(tx, neighbor, *slot)?;
                PeerDB::insert_or_replace_stacker_dbs(tx, *slot, stacker_dbs)?;
                return Ok(true);
            }
        }

        // no slots free
        return Ok(false);
    }

    /// Add a cidr prefix
    fn add_cidr_prefix(
        tx: &Transaction,
        table: &str,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        let args = params![prefix.to_bin(), mask];
        tx.execute(
            &format!(
                "INSERT OR REPLACE INTO {} (prefix, mask) VALUES (?1, ?2)",
                table
            ),
            args,
        )
        .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Remove a cidr prefix
    fn remove_cidr_prefix(
        tx: &Transaction,
        table: &str,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        let args = params![prefix.to_bin(), mask];
        tx.execute(
            &format!("DELETE FROM {} WHERE prefix = ?1 AND mask = ?2", table),
            args,
        )
        .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Get all cidr prefixes from a given table
    fn get_cidr_prefixes(conn: &DBConn, table: &str) -> Result<Vec<(PeerAddress, u32)>, db_error> {
        let sql_query = format!("SELECT prefix, mask FROM {}", table);
        let mut stmt = conn.prepare(&sql_query)?;
        let rows_res_iter = stmt
            .query_and_then(NO_PARAMS, |row| {
                let prefix = PeerAddress::from_column(row, "prefix")?;
                let mask: u32 = row.get_unwrap("mask");
                let res: Result<(PeerAddress, u32), db_error> = Ok((prefix, mask));
                res
            })
            .map_err(db_error::SqliteError)?;

        let mut ret = vec![];
        for row_res in rows_res_iter {
            ret.push(row_res?);
        }

        Ok(ret)
    }

    /// Get all deny CIDR prefixes
    pub fn get_denied_cidrs(conn: &DBConn) -> Result<Vec<(PeerAddress, u32)>, db_error> {
        PeerDB::get_cidr_prefixes(conn, "denied_prefixes")
    }

    /// Get all allow CIDR prefixes
    pub fn get_allowed_cidrs(conn: &DBConn) -> Result<Vec<(PeerAddress, u32)>, db_error> {
        PeerDB::get_cidr_prefixes(conn, "allowed_prefixes")
    }

    /// Check to see if an address is denied by one of the CIDR deny rows
    pub fn is_address_denied(conn: &DBConn, addr: &PeerAddress) -> Result<bool, db_error> {
        let denied_rows = PeerDB::get_denied_cidrs(conn)?;
        let addr_int = u128::from_be_bytes(addr.as_bytes().to_owned());

        for (prefix, mask) in denied_rows.into_iter() {
            let addr_mask = !((1u128 << (128 - mask)) - 1);
            let mask_int = u128::from_be_bytes(prefix.as_bytes().to_owned()) & addr_mask;
            if mask_int == (addr_int & addr_mask) {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Convert a prefix address and mask to its hex representation
    fn cidr_prefix_to_string(prefix: &PeerAddress, mask: u32) -> String {
        assert!(mask > 0 && mask <= 128);
        let s = to_bin(
            &(u128::from_be_bytes(prefix.as_bytes().to_owned()) & !((1u128 << (128 - mask)) - 1))
                .to_be_bytes(),
        );
        s
    }

    /// Update the given column to be equal to the given value for all addresses that match the given
    /// CIDR prefix
    fn apply_cidr_filter(
        tx: &Transaction,
        prefix: &PeerAddress,
        mask: u32,
        column: &str,
        value: i64,
    ) -> Result<(), db_error> {
        assert!(mask > 0 && mask <= 128);
        let prefix_txt = PeerDB::cidr_prefix_to_string(prefix, mask);
        let args = params![value, mask, prefix_txt];
        tx.execute(
            &format!(
                "UPDATE frontier SET {} = ?1 WHERE SUBSTR(addrbytes,1,?2) = SUBSTR(?3,1,?2)",
                column
            ),
            args,
        )
        .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Set a allowed CIDR prefix
    pub fn add_allow_cidr(
        tx: &Transaction,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        assert!(mask > 0 && mask <= 128);
        PeerDB::add_cidr_prefix(tx, "allowed_prefixes", prefix, mask)?;

        debug!("Apply allow {}/{}", &prefix, mask);
        PeerDB::apply_cidr_filter(tx, prefix, mask, "allowed", -1)?;
        Ok(())
    }

    /// Set a denied CIDR prefix
    pub fn add_deny_cidr(
        tx: &Transaction,
        prefix: &PeerAddress,
        mask: u32,
    ) -> Result<(), db_error> {
        assert!(mask > 0 && mask <= 128);
        PeerDB::add_cidr_prefix(tx, "denied_prefixes", prefix, mask)?;

        debug!("Apply deny {}/{}", &prefix, mask);
        PeerDB::apply_cidr_filter(tx, prefix, mask, "denied", i64::MAX)?;
        Ok(())
    }

    /// Get random neighbors, optionally always including allowed neighbors.
    /// Private IPs may be returned, if known.
    pub fn get_random_neighbors(
        conn: &DBConn,
        network_id: u32,
        network_epoch: u8,
        count: u32,
        block_height: u64,
        always_include_allowed: bool,
    ) -> Result<Vec<Neighbor>, db_error> {
        Self::get_fresh_random_neighbors(
            conn,
            network_id,
            network_epoch,
            0,
            count,
            block_height,
            always_include_allowed,
            false,
        )
    }

    /// Get random neighbors, optionally always including allowed neighbors
    pub fn get_fresh_random_neighbors(
        conn: &DBConn,
        network_id: u32,
        network_epoch: u8,
        min_age: u64,
        count: u32,
        block_height: u64,
        always_include_allowed: bool,
        public_only: bool,
    ) -> Result<Vec<Neighbor>, db_error> {
        let mut ret = vec![];

        // UTC time
        let now_secs = util::get_epoch_time_secs();

        if always_include_allowed {
            // always include allowed neighbors, freshness be damned
            let allow_qry = "SELECT * FROM frontier WHERE network_id = ?1 AND denied < ?2 AND (allowed < 0 OR ?3 < allowed) AND (peer_version & 0x000000ff) >= ?4";
            let allow_args = params![
                network_id,
                u64_to_sql(now_secs)?,
                u64_to_sql(now_secs)?,
                network_epoch,
            ];
            let mut allow_rows = Self::query_peers(conn, &allow_qry, allow_args)?;

            if allow_rows.len() >= (count as usize) {
                // return a random subset
                let allow_slice = allow_rows.as_mut_slice();
                allow_slice.shuffle(&mut thread_rng());
                return Ok(allow_slice[0..(count as usize)].to_vec());
            }

            ret.append(&mut allow_rows);
        }
        if (ret.len() as u32) >= count {
            return Ok(ret);
        }

        // fill in with non-allowed, randomly-chosen, fresh peers
        let use_public = if public_only { "AND public = 1" } else { "" };

        let random_peers_qry = if always_include_allowed {
            format!("SELECT * FROM frontier WHERE network_id = ?1 AND last_contact_time >= ?2 AND ?3 < expire_block_height AND denied < ?4 AND \
                 (allowed >= 0 AND allowed <= ?5) AND (peer_version & 0x000000ff) >= ?6 {use_public} ORDER BY RANDOM() LIMIT ?7")
        } else {
            format!("SELECT * FROM frontier WHERE network_id = ?1 AND last_contact_time >= ?2 AND ?3 < expire_block_height AND denied < ?4 AND \
                 (allowed < 0 OR (allowed >= 0 AND allowed <= ?5)) AND (peer_version & 0x000000ff) >= ?6 {use_public} ORDER BY RANDOM() LIMIT ?7")
        };

        let random_peers_args = params![
            network_id,
            u64_to_sql(min_age)?,
            u64_to_sql(block_height)?,
            u64_to_sql(now_secs)?,
            u64_to_sql(now_secs)?,
            network_epoch,
            (count - (ret.len() as u32)),
        ];
        let mut random_peers = Self::query_peers(conn, &random_peers_qry, random_peers_args)?;

        ret.append(&mut random_peers);
        Ok(ret)
    }

    /// Get an randomized initial set of peers.
    /// -- always include all allowed neighbors
    /// -- never include denied neighbors
    /// -- for neighbors that are neither allowed nor denied, sample them randomly as long as they're fresh.
    pub fn get_initial_neighbors(
        conn: &DBConn,
        network_id: u32,
        network_epoch: u8,
        count: u32,
        block_height: u64,
    ) -> Result<Vec<Neighbor>, db_error> {
        PeerDB::get_random_neighbors(conn, network_id, network_epoch, count, block_height, true)
    }

    /// Get a randomized set of peers for walking the peer graph.
    /// -- selects peers at random even if not allowed
    /// -- may include private IPs
    #[cfg_attr(test, mutants::skip)]
    pub fn get_random_walk_neighbors(
        conn: &DBConn,
        network_id: u32,
        network_epoch: u8,
        min_age: u64,
        count: u32,
        block_height: u64,
    ) -> Result<Vec<Neighbor>, db_error> {
        PeerDB::get_fresh_random_neighbors(
            conn,
            network_id,
            network_epoch,
            min_age,
            count,
            block_height,
            false,
            false,
        )
    }

    /// Add an IPv4 <--> ASN mapping
    /// Used during db instantiation
    fn asn4_insert(tx: &Transaction, asn4: &ASEntry4) -> Result<(), db_error> {
        tx.execute(
            "INSERT OR REPLACE INTO asn4 (prefix, mask, asn, org) VALUES (?1, ?2, ?3, ?4)",
            params![asn4.prefix, asn4.mask, asn4.asn, asn4.org,],
        )
        .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Classify an IPv4 address to its AS number.
    /// This method doesn't have to be particularly efficient since it's off the critical path.
    pub fn asn4_lookup(conn: &DBConn, addrbits: &PeerAddress) -> Result<Option<u32>, db_error> {
        // must be an IPv4 address
        if !addrbits.is_ipv4() {
            return Err(db_error::TypeError);
        }

        // NOTE: sqlite3 will use the machine's endianness here
        let addr_u32 = addrbits.ipv4_bits().unwrap();

        let qry = "SELECT * FROM asn4 WHERE prefix = (?1 & ~((1 << (32 - mask)) - 1)) ORDER BY prefix DESC LIMIT 1";
        let args = params![addr_u32];
        let rows = query_rows::<ASEntry4, _>(conn, &qry, args)?;
        match rows.len() {
            0 => Ok(None),
            _ => Ok(Some(rows[0].asn)),
        }
    }

    /// Classify an IP address to its AS number
    #[cfg_attr(test, mutants::skip)]
    pub fn asn_lookup(conn: &DBConn, addrbits: &PeerAddress) -> Result<Option<u32>, db_error> {
        if addrbits.is_ipv4() {
            PeerDB::asn4_lookup(conn, addrbits)
        } else {
            // TODO
            Ok(None)
        }
    }

    /// Count the number of nodes in a given AS
    #[cfg_attr(test, mutants::skip)]
    pub fn asn_count(conn: &DBConn, asn: u32) -> Result<u64, db_error> {
        let qry = "SELECT COUNT(*) FROM frontier WHERE asn = ?1";
        let args = params![asn];
        let count = query_count(conn, &qry, args)?;
        Ok(count as u64)
    }

    #[cfg_attr(test, mutants::skip)]
    pub fn get_frontier_size(conn: &DBConn) -> Result<u64, db_error> {
        let qry = "SELECT COUNT(*) FROM frontier";
        let count = query_count(conn, &qry, NO_PARAMS)?;
        Ok(count as u64)
    }

    pub fn get_all_peers(conn: &DBConn) -> Result<Vec<Neighbor>, db_error> {
        let qry = "SELECT * FROM frontier ORDER BY addrbytes ASC, port ASC";
        let rows = Self::query_peers(conn, &qry, NO_PARAMS)?;
        Ok(rows)
    }

    /// Find out which peers replicate a particular stacker DB.
    /// Return a randomized list of up to the given size, where all
    /// peers returned have a last-contact time greater than the given minimum age.
    pub fn find_stacker_db_replicas(
        conn: &DBConn,
        network_id: u32,
        smart_contract: &QualifiedContractIdentifier,
        min_age: u64,
        max_count: usize,
    ) -> Result<Vec<Neighbor>, db_error> {
        if max_count == 0 {
            return Ok(vec![]);
        }
        let qry = "SELECT frontier.* FROM frontier JOIN stackerdb_peers ON stackerdb_peers.peer_slot = frontier.slot WHERE stackerdb_peers.smart_contract_id = ?1 AND frontier.network_id = ?2 AND frontier.last_contact_time >= ?3 ORDER BY RANDOM() LIMIT ?4";
        let max_count_u32 = u32::try_from(max_count).unwrap_or(u32::MAX);
        let args = params![
            smart_contract.to_string(),
            network_id,
            u64_to_sql(min_age)?,
            max_count_u32,
        ];
        Self::query_peers(conn, qry, args)
    }
}

#[cfg(any(test, feature = "testing"))]
mod test {
    use clarity::vm::types::{StacksAddressExtensions, StandardPrincipalData};
    use stacks_common::types::chainstate::StacksAddress;
    use stacks_common::types::net::{PeerAddress, PeerHost};
    use stacks_common::util::hash::Hash160;

    use super::*;
    use crate::net::{Neighbor, NeighborKey};

    impl PeerDB {
        /// test the `public` flag
        pub fn is_public(
            conn: &DBConn,
            network_id: u32,
            peer_addr: &PeerAddress,
            peer_port: u16,
        ) -> Result<bool, db_error> {
            let qry = "SELECT public FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3";
            let args = params![network_id, peer_addr.to_bin(), peer_port,];
            let public: bool = query_row(conn, qry, args)?.ok_or(db_error::NotFoundError)?;
            Ok(public)
        }
    }

    /// Test storage, retrieval, and mutation of LocalPeer, including its stacker DB contract IDs
    #[test]
    fn test_local_peer() {
        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();
        let local_peer = PeerDB::get_local_peer(db.conn()).unwrap();

        assert_eq!(local_peer.network_id, 0x9abcdef0);
        assert_eq!(local_peer.parent_network_id, 12345);
        assert_eq!(local_peer.private_key_expire, 0);
        assert_eq!(
            local_peer.data_url,
            UrlString::try_from("http://foo.com".to_string()).unwrap()
        );
        assert_eq!(local_peer.port, NETWORK_P2P_PORT);
        assert_eq!(local_peer.addrbytes, PeerAddress::from_ipv4(127, 0, 0, 1));
        assert_eq!(
            local_peer.services,
            (ServiceFlags::RELAY as u16)
                | (ServiceFlags::RPC as u16)
                | (ServiceFlags::STACKERDB as u16)
        );
        assert_eq!(local_peer.stacker_dbs, vec![]);

        let mut stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x01, [0x02; 20]),
                "db-1".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x02, [0x03; 20]),
                "db-2".into(),
            ),
        ];
        stackerdbs.sort();

        db.update_local_peer(
            0x9abcdef0,
            12345,
            UrlString::try_from("http://bar.com".to_string()).unwrap(),
            4567,
            &stackerdbs,
        )
        .unwrap();

        let mut local_peer = PeerDB::get_local_peer(db.conn()).unwrap();
        local_peer.stacker_dbs.sort();

        assert_eq!(
            local_peer.data_url,
            UrlString::try_from("http://bar.com".to_string()).unwrap()
        );
        assert_eq!(local_peer.port, 4567);
        assert_eq!(local_peer.stacker_dbs, stackerdbs);
    }

    /// Test PeerDB::insert_or_replace_peer() to verify that PeerDB::get_peer() will fetch the
    /// latest peer's state.  Tests mutation of peer rows as well.
    #[test]
    fn test_peer_insert_and_retrieval() {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();

        let neighbor_before_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_before_opt, None);

        {
            let tx = db.tx_begin().unwrap();
            PeerDB::insert_or_replace_peer(&tx, &neighbor, 0).unwrap();
            tx.commit().unwrap();
        }

        let neighbor_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_opt, Some(neighbor.clone()));

        let neighbor_at_opt = PeerDB::get_peer_at(db.conn(), 0x9abcdef0, 0).unwrap();
        assert_eq!(neighbor_at_opt, Some(neighbor.clone()));

        let neighbor_not_at_opt = PeerDB::get_peer_at(db.conn(), 0x9abcdef0, 1).unwrap();
        assert_eq!(neighbor_not_at_opt, None);

        let neighbor_not_at_opt_network = PeerDB::get_peer_at(db.conn(), 0x9abcdef1, 0).unwrap();
        assert_eq!(neighbor_not_at_opt_network, None);

        {
            let tx = db.tx_begin().unwrap();
            PeerDB::insert_or_replace_peer(&tx, &neighbor, 0).unwrap();
            tx.commit().unwrap();
        }
    }

    /// Verify that PeerDB::insert_or_replace_peer() will maintain each peer's stacker DB contract
    /// IDs. New peers' contract IDs get added, and dropped peers' contract IDs get removed.
    #[test]
    fn test_insert_or_replace_stacker_dbs() {
        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();

        // the neighbors to whom this DB corresponds
        let neighbor_1 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let neighbor_2 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x10,
                ]),
                port: 12346,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02845147b61e1308d0e7fd4e801ca8e93535bd075d3f45bb2452f4415fa616ed10",
            )
            .unwrap(),
            expire_block: 23457,
            last_contact_time: 1552509643,
            allowed: -1,
            denied: -1,
            asn: 34568,
            org: 45679,
            in_degree: 2,
            out_degree: 2,
        };

        let tx = db.tx_begin().unwrap();
        PeerDB::insert_or_replace_peer(&tx, &neighbor_1, 1).unwrap();
        PeerDB::insert_or_replace_peer(&tx, &neighbor_2, 2).unwrap();
        tx.commit().unwrap();

        // basic storage and retrieval
        let mut stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x01, [0x02; 20]),
                "db-1".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x02, [0x03; 20]),
                "db-2".into(),
            ),
        ];
        stackerdbs.sort();

        let tx = db.tx_begin().unwrap();
        PeerDB::insert_or_replace_stacker_dbs(&tx, 1, &stackerdbs).unwrap();
        tx.commit().unwrap();

        let mut fetched_stackerdbs = PeerDB::get_stacker_dbs_by_slot(&db.conn, 1).unwrap();
        fetched_stackerdbs.sort();
        assert_eq!(stackerdbs, fetched_stackerdbs);

        // can add the same DBs to a different slot
        let tx = db.tx_begin().unwrap();
        PeerDB::insert_or_replace_stacker_dbs(&tx, 2, &stackerdbs).unwrap();
        tx.commit().unwrap();

        let mut fetched_stackerdbs = PeerDB::get_stacker_dbs_by_slot(&db.conn, 2).unwrap();
        fetched_stackerdbs.sort();
        assert_eq!(stackerdbs, fetched_stackerdbs);

        // adding DBs to the same slot just grows the total list
        let mut new_stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x03, [0x04; 20]),
                "db-3".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x04, [0x05; 20]),
                "db-5".into(),
            ),
        ];
        new_stackerdbs.sort();

        let mut all_stackerdbs = stackerdbs.clone();
        all_stackerdbs.extend_from_slice(&new_stackerdbs);
        all_stackerdbs.sort();

        let tx = db.tx_begin().unwrap();
        PeerDB::insert_or_replace_stacker_dbs(&tx, 1, &new_stackerdbs).unwrap();
        tx.commit().unwrap();

        let mut fetched_stackerdbs = PeerDB::get_stacker_dbs_by_slot(&db.conn, 1).unwrap();
        fetched_stackerdbs.sort();
        assert_eq!(fetched_stackerdbs, all_stackerdbs);

        // can't add a DB to a non-existant peer
        let tx = db.tx_begin().unwrap();
        PeerDB::insert_or_replace_stacker_dbs(&tx, 3, &stackerdbs).unwrap_err();
        tx.commit().unwrap();

        // deleting a peer deletes the associated DB
        let tx = db.tx_begin().unwrap();
        PeerDB::drop_peer(
            &tx,
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap();
        tx.commit().unwrap();

        // can't get the DB
        let fetched_stackerdbs = PeerDB::get_stacker_dbs_by_slot(&db.conn, 1).unwrap();
        assert_eq!(fetched_stackerdbs, vec![]);
    }

    /// Test PeerDB::try_insert_peer() with no stacker DB contracts.  Simply verifies storage and
    /// retrieval works.
    #[test]
    fn test_try_insert_peer() {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();

        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, true);
        }

        let neighbor_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_opt, Some(neighbor.clone()));

        // idempotent
        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, true);
        }

        // put a peer in all the slots
        let mut new_neighbor = neighbor.clone();
        new_neighbor.addr.port += 1;
        let slots = PeerDB::peer_slots(
            db.conn(),
            neighbor.addr.network_id,
            &neighbor.addr.addrbytes,
            neighbor.addr.port,
        )
        .unwrap();
        for slot in slots {
            let tx = db.tx_begin().unwrap();
            PeerDB::insert_or_replace_peer(&tx, &neighbor, slot).unwrap();
            tx.commit().unwrap();
        }

        // succeeds because it's the same peer
        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, true);
        }

        // put neighbor at new_neighbor's slots
        let slots = PeerDB::peer_slots(
            db.conn(),
            new_neighbor.addr.network_id,
            &new_neighbor.addr.addrbytes,
            new_neighbor.addr.port,
        )
        .unwrap();
        for slot in slots {
            let tx = db.tx_begin().unwrap();
            PeerDB::insert_or_replace_peer(&tx, &neighbor, slot).unwrap();
            tx.commit().unwrap();
        }

        // fails because it's a different peer
        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &new_neighbor, &[]).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, false);
        }
    }

    /// Test PeerDB::try_insert_peer() with different lists of stacker DB contract IDs.
    /// Verify that the peer's contract IDs are updated on each call to try_insert_peer()
    #[test]
    fn test_try_insert_peer_with_stackerdbs() {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let key1 = Secp256k1PrivateKey::new();

        let path = "/tmp/test-peerdb-try_insert_peer_with_stackerdbs.db".to_string();
        if fs::metadata(&path).is_ok() {
            fs::remove_file(&path).unwrap();
        }
        let mut db = PeerDB::connect(
            &path,
            true,
            0x9abcdef0,
            12345,
            Some(key1.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();

        let mut stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x01, [0x02; 20]),
                "db-1".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x02, [0x03; 20]),
                "db-2".into(),
            ),
        ];
        stackerdbs.sort();

        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &stackerdbs).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, true);
        }

        let neighbor_opt = PeerDB::get_peer(
            db.conn(),
            0x9abcdef0,
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f,
            ]),
            12345,
        )
        .unwrap();
        assert_eq!(neighbor_opt, Some(neighbor.clone()));

        let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        neighbor_stackerdbs.sort();
        assert_eq!(neighbor_stackerdbs, stackerdbs);

        // insert new stacker DBs -- keep one the same, and add a different one
        let mut changed_stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x01, [0x02; 20]),
                "db-1".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x03, [0x04; 20]),
                "db-3".into(),
            ),
        ];
        changed_stackerdbs.sort();

        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &changed_stackerdbs).unwrap();
            tx.commit().unwrap();

            // peer already present
            assert_eq!(res, true);
        }

        let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        neighbor_stackerdbs.sort();
        assert_eq!(neighbor_stackerdbs, changed_stackerdbs);

        // clear stacker DBs
        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap();
            tx.commit().unwrap();

            // peer already present
            assert_eq!(res, true);
        }

        let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        neighbor_stackerdbs.sort();
        assert_eq!(neighbor_stackerdbs, []);

        // add back stacker DBs
        let mut new_stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x04, [0x05; 20]),
                "db-4".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x05, [0x06; 20]),
                "db-5".into(),
            ),
        ];
        new_stackerdbs.sort();

        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &new_stackerdbs).unwrap();
            tx.commit().unwrap();

            // peer already present
            assert_eq!(res, true);
        }

        let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        neighbor_stackerdbs.sort();
        assert_eq!(neighbor_stackerdbs, new_stackerdbs);

        // replace all stacker DBs.
        // Do it twice -- it should be idempotent
        for _ in 0..2 {
            let mut replace_stackerdbs = vec![
                QualifiedContractIdentifier::new(
                    StandardPrincipalData(0x06, [0x07; 20]),
                    "db-6".into(),
                ),
                QualifiedContractIdentifier::new(
                    StandardPrincipalData(0x07, [0x08; 20]),
                    "db-7".into(),
                ),
            ];
            replace_stackerdbs.sort();

            {
                let tx = db.tx_begin().unwrap();
                let res = PeerDB::try_insert_peer(&tx, &neighbor, &replace_stackerdbs).unwrap();
                tx.commit().unwrap();

                // peer already present
                assert_eq!(res, true);
            }

            let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
            neighbor_stackerdbs.sort();
            assert_eq!(neighbor_stackerdbs, replace_stackerdbs);
        }

        // a peer re-keying will drop its stacker DBs
        let new_neighbor = neighbor.clone();

        // drop the peer.  the stacker DBs should disappear as well
        {
            let tx = db.tx_begin().unwrap();
            PeerDB::drop_peer(
                &tx,
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let deleted_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        assert_eq!(deleted_stackerdbs.len(), 0);
    }

    /// Test PeerDB::find_stacker_db_replicas().  Verifies that we can find a list of neighbors
    /// that serve a particular stacker DB, given their contract IDs
    #[test]
    fn test_find_stacker_db_replicas() {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let key1 = Secp256k1PrivateKey::new();

        let path = "/tmp/test-peerdb-find_stacker_db_replicas.db".to_string();
        if fs::metadata(&path).is_ok() {
            fs::remove_file(&path).unwrap();
        }
        let mut db = PeerDB::connect(
            &path,
            true,
            0x9abcdef0,
            12345,
            Some(key1.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();

        let mut stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x01, [0x02; 20]),
                "db-1".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x02, [0x03; 20]),
                "db-2".into(),
            ),
        ];
        stackerdbs.sort();

        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &stackerdbs).unwrap();
            tx.commit().unwrap();

            assert_eq!(res, true);
        }

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &stackerdbs[0], 0, 1).unwrap();
        assert_eq!(replicas.len(), 1);
        assert_eq!(replicas[0], neighbor);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &stackerdbs[0], 0, 2).unwrap();
        assert_eq!(replicas.len(), 1);
        assert_eq!(replicas[0], neighbor);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &stackerdbs[0], 0, 0).unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef1, &stackerdbs[0], 0, 1).unwrap();
        assert_eq!(replicas.len(), 0);

        // insert new stacker DBs -- keep one the same, and add a different one
        let mut changed_stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x01, [0x02; 20]),
                "db-1".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x03, [0x04; 20]),
                "db-3".into(),
            ),
        ];
        changed_stackerdbs.sort();

        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &changed_stackerdbs).unwrap();
            tx.commit().unwrap();

            // peer already present, and we were able to update
            assert_eq!(res, true);
        }

        let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        neighbor_stackerdbs.sort();
        assert_eq!(neighbor_stackerdbs, changed_stackerdbs);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &changed_stackerdbs[0], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 1);
        assert_eq!(replicas[0], neighbor);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &changed_stackerdbs[1], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 1);
        assert_eq!(replicas[0], neighbor);

        // query stacker DBs filtering by last-contact time
        let replicas = PeerDB::find_stacker_db_replicas(
            &db.conn,
            0x9abcdef0,
            &changed_stackerdbs[1],
            1552509641,
            1,
        )
        .unwrap();
        assert_eq!(replicas.len(), 1);
        assert_eq!(replicas[0], neighbor);

        let replicas = PeerDB::find_stacker_db_replicas(
            &db.conn,
            0x9abcdef0,
            &changed_stackerdbs[1],
            1552509642,
            1,
        )
        .unwrap();
        assert_eq!(replicas.len(), 1);
        assert_eq!(replicas[0], neighbor);

        let replicas = PeerDB::find_stacker_db_replicas(
            &db.conn,
            0x9abcdef0,
            &changed_stackerdbs[1],
            1552509643,
            1,
        )
        .unwrap();
        assert_eq!(replicas.len(), 0);

        // clear stacker DBs
        {
            let tx = db.tx_begin().unwrap();
            let res = PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap();
            tx.commit().unwrap();

            // peer already present, and we were able to update
            assert_eq!(res, true);
        }

        let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
        neighbor_stackerdbs.sort();
        assert_eq!(neighbor_stackerdbs, []);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &changed_stackerdbs[0], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &changed_stackerdbs[1], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 0);

        let mut replace_stackerdbs = vec![
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x06, [0x07; 20]),
                "db-6".into(),
            ),
            QualifiedContractIdentifier::new(
                StandardPrincipalData(0x07, [0x08; 20]),
                "db-7".into(),
            ),
        ];
        replace_stackerdbs.sort();

        // replace all stacker DBs.
        // Do it twice -- it should be idempotent
        for _ in 0..2 {
            {
                let tx = db.tx_begin().unwrap();
                let res = PeerDB::try_insert_peer(&tx, &neighbor, &replace_stackerdbs).unwrap();
                tx.commit().unwrap();

                // peer already present and we were able to update
                assert_eq!(res, true);
            }

            let mut neighbor_stackerdbs = db.get_peer_stacker_dbs(&neighbor).unwrap();
            neighbor_stackerdbs.sort();
            assert_eq!(neighbor_stackerdbs, replace_stackerdbs);

            let replicas =
                PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdee0, &stackerdbs[0], 0, 1)
                    .unwrap();
            assert_eq!(replicas.len(), 0);

            let replicas =
                PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdee0, &stackerdbs[1], 0, 1)
                    .unwrap();
            assert_eq!(replicas.len(), 0);

            let replicas = PeerDB::find_stacker_db_replicas(
                &db.conn,
                0x9abcdef0,
                &changed_stackerdbs[0],
                0,
                1,
            )
            .unwrap();
            assert_eq!(replicas.len(), 0);

            let replicas = PeerDB::find_stacker_db_replicas(
                &db.conn,
                0x9abcdef0,
                &changed_stackerdbs[1],
                0,
                1,
            )
            .unwrap();
            assert_eq!(replicas.len(), 0);

            let replicas = PeerDB::find_stacker_db_replicas(
                &db.conn,
                0x9abcdef0,
                &replace_stackerdbs[0],
                0,
                1,
            )
            .unwrap();
            assert_eq!(replicas.len(), 1);
            assert_eq!(replicas[0], neighbor);

            let replicas = PeerDB::find_stacker_db_replicas(
                &db.conn,
                0x9abcdef0,
                &replace_stackerdbs[1],
                0,
                1,
            )
            .unwrap();
            assert_eq!(replicas.len(), 1);
            assert_eq!(replicas[0], neighbor);
        }

        // drop the peer.  the stacker DBs should disappear as well
        {
            let tx = db.tx_begin().unwrap();
            PeerDB::drop_peer(
                &tx,
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &stackerdbs[0], 0, 1).unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &stackerdbs[1], 0, 1).unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &changed_stackerdbs[0], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &changed_stackerdbs[1], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &replace_stackerdbs[0], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 0);

        let replicas =
            PeerDB::find_stacker_db_replicas(&db.conn, 0x9abcdef0, &replace_stackerdbs[1], 0, 1)
                .unwrap();
        assert_eq!(replicas.len(), 0);
    }

    /// Tests DB instantiation with initial neighbors. Verifies that initial neighbors are present in the
    /// DB, and can be loaded with PeerDB::get_initial_neighbors()
    #[test]
    fn test_initial_neighbors() {
        let mut initial_neighbors = vec![];
        let now_secs = util::get_epoch_time_secs();
        for i in 0..10 {
            initial_neighbors.push(Neighbor {
                addr: NeighborKey {
                    peer_version: 0x12345678,
                    network_id: 0x9abcdef0,
                    addrbytes: PeerAddress([i as u8; 16]),
                    port: i,
                },
                public_key: Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new()),
                expire_block: (i + 23456) as u64,
                last_contact_time: (1552509642 + (i as u64)),
                allowed: (now_secs + 600) as i64,
                denied: -1,
                asn: (34567 + i) as u32,
                org: (45678 + i) as u32,
                in_degree: 1,
                out_degree: 1,
            });
        }

        for i in 10..20 {
            initial_neighbors.push(Neighbor {
                addr: NeighborKey {
                    peer_version: 0x12345678,
                    network_id: 0x9abcdef0,
                    addrbytes: PeerAddress([i as u8; 16]),
                    port: i,
                },
                public_key: Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new()),
                expire_block: (i + 23456) as u64,
                last_contact_time: (1552509642 + (i as u64)),
                allowed: 0,
                denied: -1,
                asn: (34567 + i) as u32,
                org: (45678 + i) as u32,
                in_degree: 1,
                out_degree: 1,
            });
        }

        fn are_present(ne: &[Neighbor], nei: &[Neighbor]) -> bool {
            for n in ne {
                let mut found = false;
                for ni in nei {
                    if *n == *ni {
                        found = true;
                        break;
                    }
                }
                if !found {
                    return false;
                }
            }
            return true;
        }

        let db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &[],
            &initial_neighbors,
        )
        .unwrap();

        let n5 = PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 0x78, 5, 23455).unwrap();
        assert!(are_present(&n5, &initial_neighbors));

        let n10 = PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 0x78, 10, 23455).unwrap();
        assert!(are_present(&n10, &initial_neighbors));

        let n20 = PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 0x78, 20, 23455).unwrap();
        assert!(are_present(&initial_neighbors, &n20));

        let n15_fresh =
            PeerDB::get_initial_neighbors(db.conn(), 0x9abcdef0, 0x78, 15, 23456 + 14).unwrap();
        assert!(are_present(
            &n15_fresh[10..15].to_vec(),
            &initial_neighbors[10..20].to_vec()
        ));
        for n in &n15_fresh[10..15] {
            assert!(n.expire_block > 23456 + 14);
            assert!(n.allowed == 0);
        }

        for neighbor in &initial_neighbors {
            assert!(PeerDB::is_initial_peer(
                db.conn(),
                neighbor.addr.network_id,
                &neighbor.addr.addrbytes,
                neighbor.addr.port
            )
            .unwrap());
        }
    }

    /// Tests DB instantiation with initial neighbors, and verifies that initial neighbors can be
    /// queried by epoch -- only peers with the current or newer epoch will be fetched.
    #[test]
    fn test_get_neighbors_in_current_epoch() {
        let mut initial_neighbors = vec![];
        let now_secs = util::get_epoch_time_secs();
        for i in 0..10 {
            // epoch 2.0 neighbors
            initial_neighbors.push(Neighbor {
                addr: NeighborKey {
                    peer_version: 0x18000000,
                    network_id: 0x9abcdef0,
                    addrbytes: PeerAddress([i as u8; 16]),
                    port: i,
                },
                public_key: Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new()),
                expire_block: (i + 23456) as u64,
                last_contact_time: (1552509642 + (i as u64)),
                allowed: -1,
                denied: -1,
                asn: (34567 + i) as u32,
                org: (45678 + i) as u32,
                in_degree: 1,
                out_degree: 1,
            });
        }

        for i in 10..20 {
            // epoch 2.05 neighbors
            initial_neighbors.push(Neighbor {
                addr: NeighborKey {
                    peer_version: 0x18000005,
                    network_id: 0x9abcdef0,
                    addrbytes: PeerAddress([i as u8; 16]),
                    port: i,
                },
                public_key: Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new()),
                expire_block: (i + 23456) as u64,
                last_contact_time: (1552509642 + (i as u64)),
                allowed: -1,
                denied: -1,
                asn: (34567 + i) as u32,
                org: (45678 + i) as u32,
                in_degree: 1,
                out_degree: 1,
            });
        }

        fn are_present(ne: &[Neighbor], nei: &[Neighbor]) -> bool {
            for n in ne {
                let mut found = false;
                for ni in nei {
                    if *n == *ni {
                        found = true;
                        break;
                    }
                }
                if !found {
                    eprintln!("Not found: {:?}", &n);
                    return false;
                }
            }
            return true;
        }

        let db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &[],
            &initial_neighbors,
        )
        .unwrap();

        // epoch 2.0
        let n5 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x00, 5, 23455, false).unwrap();
        assert_eq!(n5.len(), 5);
        assert!(are_present(&n5, &initial_neighbors));

        let n10 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x00, 10, 23455, false).unwrap();
        assert_eq!(n10.len(), 10);
        assert!(are_present(&n10, &initial_neighbors));

        let n20 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x00, 20, 23455, false).unwrap();
        assert_eq!(n20.len(), 20);
        assert!(are_present(&initial_neighbors, &n20));

        // epoch 2.05
        let n5 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x05, 5, 23455, false).unwrap();
        assert_eq!(n5.len(), 5);
        assert!(are_present(&n5, &initial_neighbors));
        for n in n5 {
            assert_eq!(n.addr.peer_version, 0x18000005);
        }

        let n10 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x05, 10, 23455, false).unwrap();
        assert_eq!(n10.len(), 10);
        assert!(are_present(&n10, &initial_neighbors));
        for n in n10 {
            assert_eq!(n.addr.peer_version, 0x18000005);
        }

        let n20 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x05, 20, 23455, false).unwrap();
        assert_eq!(n20.len(), 10); // only 10 such neighbors are recent enough
        assert!(are_present(&n20, &initial_neighbors));
        for n in n20 {
            assert_eq!(n.addr.peer_version, 0x18000005);
        }

        // post epoch 2.05 -- no such neighbors
        let n20 =
            PeerDB::get_random_neighbors(db.conn(), 0x9abcdef0, 0x06, 20, 23455, false).unwrap();
        assert_eq!(n20.len(), 0);
    }

    /// Verifies that PeerDB::asn4_lookup() correctly classifies IPv4 address into their AS numbers
    #[test]
    fn asn4_insert_lookup() {
        let asn4_table = vec![
            ASEntry4 {
                prefix: 0x01020200,
                mask: 24,
                asn: 1,
                org: 0,
            },
            ASEntry4 {
                prefix: 0x01020200,
                mask: 23,
                asn: 2,
                org: 0,
            },
            ASEntry4 {
                prefix: 0x01020000,
                mask: 16,
                asn: 3,
                org: 0,
            },
            ASEntry4 {
                prefix: 0x02030000,
                mask: 16,
                asn: 4,
                org: 0,
            },
        ];

        let db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &asn4_table,
            &[],
        )
        .unwrap();

        let asn1_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01, 0x02,
            0x02, 0x04,
        ]);
        let asn2_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01, 0x02,
            0x03, 0x10,
        ]);
        let asn3_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01, 0x02,
            0x13, 0x10,
        ]);
        let asn4_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x02, 0x03,
            0x13, 0x10,
        ]);

        // classify addresses
        let asn1_opt = PeerDB::asn4_lookup(db.conn(), &asn1_addr).unwrap();
        assert_eq!(asn1_opt, Some(1));

        let asn2_opt = PeerDB::asn4_lookup(db.conn(), &asn2_addr).unwrap();
        assert_eq!(asn2_opt, Some(2));

        let asn3_opt = PeerDB::asn4_lookup(db.conn(), &asn3_addr).unwrap();
        assert_eq!(asn3_opt, Some(3));

        let asn4_opt = PeerDB::asn4_lookup(db.conn(), &asn4_addr).unwrap();
        assert_eq!(asn4_opt, Some(4));

        // invalid -- not an ipv4 address
        let asn4_invalid_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xff, 0xff, 0x02, 0x03,
            0x13, 0x10,
        ]);
        let asn_invalid_opt = PeerDB::asn4_lookup(db.conn(), &asn4_invalid_addr);
        match asn_invalid_opt {
            Ok(_) => assert!(false),
            Err(db_error::TypeError) => assert!(true),
            Err(_) => assert!(false),
        }

        // not present
        let asn4_missing_addr = PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x02, 0x04,
            0x13, 0x10,
        ]);
        let asn_missing_opt = PeerDB::asn4_lookup(db.conn(), &asn4_missing_addr).unwrap();
        assert_eq!(asn_missing_opt, None);
    }

    /// Verifies that PeerDB::set_deny_peer() and PeerDB::set_allow_peer() will mark peers'
    /// `denied` and `allowed` columns appropriately.
    #[test]
    fn test_peer_preemptive_deny_allow() {
        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();
        {
            let tx = db.tx_begin().unwrap();
            PeerDB::set_deny_peer(&tx, 0x9abcdef0, &PeerAddress([0x1; 16]), 12345, 10000000)
                .unwrap();
            PeerDB::set_allow_peer(&tx, 0x9abcdef0, &PeerAddress([0x2; 16]), 12345, 20000000)
                .unwrap();
            tx.commit().unwrap();
        }

        let peer_denied = PeerDB::get_peer(db.conn(), 0x9abcdef0, &PeerAddress([0x1; 16]), 12345)
            .unwrap()
            .unwrap();
        let peer_allowed = PeerDB::get_peer(db.conn(), 0x9abcdef0, &PeerAddress([0x2; 16]), 12345)
            .unwrap()
            .unwrap();

        assert_eq!(peer_denied.denied, 10000000);
        assert_eq!(peer_allowed.allowed, 20000000);
    }

    /// Verifies that PeerDB::add_cidr_prefix(), PeerDB::get_denied_cidrs(), and
    /// PeerDB::get_allowed_cidrs() correctly store and load CIDR prefixes
    #[test]
    fn test_peer_cidr_lists() {
        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();
        {
            let tx = db.tx_begin().unwrap();
            PeerDB::add_cidr_prefix(&tx, "denied_prefixes", &PeerAddress([0x1; 16]), 64).unwrap();
            PeerDB::add_cidr_prefix(&tx, "allowed_prefixes", &PeerAddress([0x2; 16]), 96).unwrap();
            tx.commit().unwrap();
        }

        let deny_cidrs = PeerDB::get_denied_cidrs(db.conn()).unwrap();
        let allow_cidrs = PeerDB::get_allowed_cidrs(db.conn()).unwrap();

        assert_eq!(deny_cidrs, vec![(PeerAddress([0x1; 16]), 64)]);
        assert_eq!(allow_cidrs, vec![(PeerAddress([0x2; 16]), 96)]);
    }

    /// Verifies that an IPv4 peer will be treated as denied if its IPv4 CIDR prefix is denied.
    /// Tests PeerDB::is_address_denied()
    #[test]
    fn test_peer_is_denied() {
        let mut db =
            PeerDB::connect_memory(0x9abcdef0, 12345, 0, "http://foo.com".into(), &[], &[])
                .unwrap();
        {
            let tx = db.tx_begin().unwrap();
            PeerDB::add_deny_cidr(
                &tx,
                &PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ]),
                64,
            )
            .unwrap();
            PeerDB::add_deny_cidr(
                &tx,
                &PeerAddress([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x11,
                    0x22, 0x33, 0x44,
                ]),
                128,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        assert!(PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(!PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(!PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01
            ])
        )
        .unwrap());
        assert!(PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x11, 0x22,
                0x33, 0x44
            ])
        )
        .unwrap());
        assert!(!PeerDB::is_address_denied(
            db.conn(),
            &PeerAddress([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x11, 0x22,
                0x33, 0x45
            ])
        )
        .unwrap());
    }

    /// Verifies that an IPv4 address can be denied and later allowed by a change in denied/allowed CIDR prefixes.
    /// Tests that a peer will go from having a positive denied value to a negative denied value
    /// when its CIDR prefix is explicitly allowed.
    #[test]
    fn test_peer_deny_allow_cidr() {
        let neighbor_1 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 12345,
            denied: 67890,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let neighbor_2 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
                    0x1d, 0x1e, 0x1f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02287c1f1b280b5dde764b146976f6bad3fb485a3df9b1ad2d8ddc5719e7e91ff2",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 12345,
            denied: 67890,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &[],
            &[neighbor_1.clone(), neighbor_2.clone()],
        )
        .unwrap();

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        assert_eq!(n1.allowed, 12345);
        assert_eq!(n1.denied, 67890);

        {
            // ban peer 1 by banning a prefix
            let tx = db.tx_begin().unwrap();
            PeerDB::add_deny_cidr(
                &tx,
                &PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ]),
                64,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();
        assert_eq!(n1.allowed, 12345);
        assert_eq!(n1.denied, i64::MAX);
        assert_eq!(n2.allowed, 12345);
        assert_eq!(n2.denied, 67890);

        {
            // unban peer 1 by unbanning a (different) prefix
            let tx = db.tx_begin().unwrap();
            PeerDB::add_allow_cidr(
                &tx,
                &PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ]),
                48,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();

        assert_eq!(n1.allowed, -1);
        assert_eq!(n1.denied, i64::MAX);
        assert_eq!(n2.allowed, 12345);
        assert_eq!(n2.denied, 67890);
    }

    /// Tests that PeerDB::refresh_allowed() and PeerDB::refresh_denied() re-apply CIDR allow/deny
    /// rules to the DB.  Peers that match an allowed CIDR prefix remain allowed (or, if not
    /// allowed, are marked as allowed), and peers that match a denied CIDR prefix remain denied
    /// (or are marked as denied if the new prefixes require it).
    #[test]
    fn test_peer_refresh_cidr() {
        let neighbor_1 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 1234,
            denied: 5678,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let neighbor_2 = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
                    0x1d, 0x1e, 0x1f,
                ]),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02287c1f1b280b5dde764b146976f6bad3fb485a3df9b1ad2d8ddc5719e7e91ff2",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: 1234,
            denied: 5678,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let mut db = PeerDB::connect_memory(
            0x9abcdef0,
            12345,
            0,
            "http://foo.com".into(),
            &[],
            &[neighbor_1.clone(), neighbor_2.clone()],
        )
        .unwrap();
        {
            let tx = db.tx_begin().unwrap();
            PeerDB::add_cidr_prefix(&tx, "denied_prefixes", &PeerAddress([0x00; 16]), 8).unwrap();
            PeerDB::add_cidr_prefix(&tx, "allowed_prefixes", &PeerAddress([0x01; 16]), 8).unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();

        assert_eq!(n1.denied, 5678);
        assert_eq!(n2.denied, 5678);

        assert_eq!(n1.allowed, 1234);
        assert_eq!(n2.allowed, 1234);

        {
            let tx = db.tx_begin().unwrap();
            PeerDB::refresh_denies(&tx).unwrap();
            PeerDB::refresh_allows(&tx).unwrap();
            tx.commit().unwrap();
        }

        let n1 = PeerDB::get_peer(
            db.conn(),
            neighbor_1.addr.network_id,
            &neighbor_1.addr.addrbytes,
            neighbor_1.addr.port,
        )
        .unwrap()
        .unwrap();
        let n2 = PeerDB::get_peer(
            db.conn(),
            neighbor_2.addr.network_id,
            &neighbor_2.addr.addrbytes,
            neighbor_2.addr.port,
        )
        .unwrap()
        .unwrap();

        assert_eq!(n1.denied, i64::MAX);
        assert_eq!(n2.denied, 0); // refreshed; no longer denied

        assert_eq!(n1.allowed, 0);
        assert_eq!(n2.allowed, 0);
    }

    /// Test PeerDB::connect() with different private keys.  Verify that LocalPeer reflects the
    /// latest key.
    #[test]
    fn test_connect_new_key() {
        let key1 = Secp256k1PrivateKey::new();
        let key2 = Secp256k1PrivateKey::new();

        let path = "/tmp/test-connect-new-key.db".to_string();
        if fs::metadata(&path).is_ok() {
            fs::remove_file(&path).unwrap();
        }

        let db = PeerDB::connect(
            &path,
            true,
            0x80000000,
            0,
            Some(key1.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();
        let local_peer = PeerDB::get_local_peer(db.conn()).unwrap();
        assert_eq!(local_peer.private_key, key1);

        assert!(fs::metadata(&path).is_ok());

        let db = PeerDB::connect(
            &path,
            true,
            0x80000000,
            0,
            None,
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();
        let local_peer = PeerDB::get_local_peer(db.conn()).unwrap();
        assert_eq!(local_peer.private_key, key1);

        let db = PeerDB::connect(
            &path,
            true,
            0x80000000,
            0,
            Some(key2.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();
        let local_peer = PeerDB::get_local_peer(db.conn()).unwrap();
        assert_eq!(local_peer.private_key, key2);
    }

    /// Test DB instantiation -- it must work.
    #[test]
    fn test_db_instantiation() {
        let key1 = Secp256k1PrivateKey::new();

        let path = "/tmp/test-peerdb-instantiation.db".to_string();
        if fs::metadata(&path).is_ok() {
            fs::remove_file(&path).unwrap();
        }

        let db = PeerDB::connect(
            &path,
            true,
            0x80000000,
            0,
            Some(key1.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();
    }

    /// Test `public` setting in DB migration
    #[test]
    fn test_db_schema_3_public_ip_migration() {
        let key = Secp256k1PrivateKey::new();

        let path = "/tmp/test-peerdb-schema-3-public-ip-migration.db".to_string();
        if fs::metadata(&path).is_ok() {
            fs::remove_file(&path).unwrap();
        }
        let mut db = PeerDB::connect(
            &path,
            true,
            0x80000000,
            0,
            Some(key.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();

        let private_addrbytes = [
            PeerAddress::from_ipv4(127, 0, 0, 1),
            PeerAddress::from_ipv4(192, 168, 0, 1),
            PeerAddress::from_ipv4(172, 16, 0, 1),
            PeerAddress::from_ipv4(10, 0, 0, 1),
            PeerAddress([
                0xfc, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                0x0d, 0x0e,
            ]),
            PeerAddress([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x01,
            ]),
        ];

        let public_addrbytes = [
            PeerAddress::from_ipv4(1, 2, 3, 4),
            PeerAddress([
                0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
                0xff, 0x00,
            ]),
        ];

        let mut neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress::from_ipv4(127, 0, 0, 1),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        // force public and see if it gets reverted
        let tx = db.tx_begin().unwrap();

        for private in private_addrbytes.iter() {
            neighbor.addr.addrbytes = private.clone();
            neighbor.public_key = Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new());
            assert!(PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap());
        }
        for public in public_addrbytes.iter() {
            neighbor.addr.addrbytes = public.clone();
            neighbor.public_key = Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new());
            assert!(PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap());
        }
        tx.execute("UPDATE frontier SET public = 1", params![])
            .unwrap();
        tx.commit().unwrap();

        // make sure they're all listed as public (even if erroneously)
        for private in private_addrbytes.iter() {
            assert!(PeerDB::is_public(
                &db.conn,
                neighbor.addr.network_id,
                private,
                neighbor.addr.port
            )
            .unwrap());
        }
        for public in public_addrbytes.iter() {
            assert!(PeerDB::is_public(
                &db.conn,
                neighbor.addr.network_id,
                public,
                neighbor.addr.port
            )
            .unwrap());
        }

        let tx = db.tx_begin().unwrap();
        PeerDB::update_peerdb_public_addrs(&tx).unwrap();

        // fixed
        for private in private_addrbytes.iter() {
            assert!(
                !PeerDB::is_public(&tx, neighbor.addr.network_id, private, neighbor.addr.port)
                    .unwrap()
            );
        }
        for public in public_addrbytes.iter() {
            assert!(
                PeerDB::is_public(&tx, neighbor.addr.network_id, public, neighbor.addr.port)
                    .unwrap()
            );
        }

        // now do the opposite
        tx.execute("UPDATE frontier SET public = 0", params![])
            .unwrap();
        tx.commit().unwrap();

        let tx = db.tx_begin().unwrap();
        PeerDB::update_peerdb_public_addrs(&tx).unwrap();

        // fixed
        for private in private_addrbytes.iter() {
            assert!(
                !PeerDB::is_public(&tx, neighbor.addr.network_id, private, neighbor.addr.port)
                    .unwrap()
            );
        }
        for public in public_addrbytes.iter() {
            assert!(
                PeerDB::is_public(&tx, neighbor.addr.network_id, public, neighbor.addr.port)
                    .unwrap()
            );
        }
        tx.commit().unwrap();
    }

    /// Verify that multiple peers with the same public key are coalesced by last-contact-time
    #[test]
    fn test_query_peers() {
        let key = Secp256k1PrivateKey::new();

        let path = "/tmp/test-query-peers.db".to_string();
        if fs::metadata(&path).is_ok() {
            fs::remove_file(&path).unwrap();
        }
        let mut db = PeerDB::connect(
            &path,
            true,
            0x80000000,
            0,
            Some(key.clone()),
            i64::MAX as u64,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            12345,
            UrlString::try_from("http://foo.com").unwrap(),
            &[],
            None,
            &[],
        )
        .unwrap();

        let mut neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress::from_ipv4(127, 0, 0, 1),
                port: 12345,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };

        let tx = db.tx_begin().unwrap();
        for i in 0..10 {
            neighbor.addr.port = (i + 1024) as u16;
            neighbor.last_contact_time = (i + 1552509642) as u64;
            assert!(PeerDB::try_insert_peer(&tx, &neighbor, &[]).unwrap());
        }
        tx.commit().unwrap();

        // only one peer returned, and it's the one with the highest last-contact time
        let mut peers = PeerDB::query_peers(
            &db.conn,
            "SELECT * FROM frontier WHERE network_id = ?1 AND addrbytes = ?2 AND port = ?3",
            params![
                &neighbor.addr.network_id,
                &to_bin(neighbor.addr.addrbytes.as_bytes()),
                &neighbor.addr.port
            ],
        )
        .unwrap();
        assert_eq!(peers.len(), 1);

        let peer = peers.pop().unwrap();
        assert_eq!(peer.addr.port, 1033);
        assert_eq!(peer.last_contact_time, 1552509651);
    }
}
