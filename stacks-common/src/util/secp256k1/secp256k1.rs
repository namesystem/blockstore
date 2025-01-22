// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
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

use ::secp256k1;
use ::secp256k1::ecdsa::{
    RecoverableSignature as LibSecp256k1RecoverableSignature, RecoveryId as LibSecp256k1RecoveryID,
    Signature as LibSecp256k1Signature,
};
pub use ::secp256k1::Error;
use ::secp256k1::{
    constants as LibSecp256k1Constants, Error as LibSecp256k1Error, Message as LibSecp256k1Message,
    PublicKey as LibSecp256k1PublicKey, Secp256k1, SecretKey as LibSecp256k1PrivateKey,
};
use rand::{thread_rng, RngCore};
use serde::de::{Deserialize, Error as de_Error};
use serde::ser::Error as ser_Error;
use serde::Serialize;

use super::MessageSignature;
use crate::types::{PrivateKey, PublicKey};
use crate::util::hash::{hex_bytes, to_hex, Sha256Sum};

// per-thread Secp256k1 context
thread_local!(static _secp256k1: Secp256k1<secp256k1::All> = Secp256k1::new());

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Hash)]
pub struct Secp256k1PublicKey {
    // serde is broken for secp256k1, so do it ourselves
    #[serde(
        serialize_with = "secp256k1_pubkey_serialize",
        deserialize_with = "secp256k1_pubkey_deserialize"
    )]
    key: LibSecp256k1PublicKey,
    compressed: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub struct Secp256k1PrivateKey {
    // serde is broken for secp256k1, so do it ourselves
    #[serde(
        serialize_with = "secp256k1_privkey_serialize",
        deserialize_with = "secp256k1_privkey_deserialize"
    )]
    key: LibSecp256k1PrivateKey,
    compress_public: bool,
}

impl MessageSignature {
    pub fn empty() -> MessageSignature {
        // NOTE: this cannot be a valid signature
        MessageSignature([0u8; 65])
    }

    #[cfg(any(test, feature = "testing"))]
    // test method for generating place-holder data
    pub fn from_raw(sig: &[u8]) -> MessageSignature {
        let mut buf = [0u8; 65];
        if sig.len() < 65 {
            buf.copy_from_slice(sig);
        } else {
            buf.copy_from_slice(&sig[..65]);
        }
        MessageSignature(buf)
    }

    pub fn from_secp256k1_recoverable(sig: &LibSecp256k1RecoverableSignature) -> MessageSignature {
        let (recid, bytes) = sig.serialize_compact();
        let mut ret_bytes = [0u8; 65];
        let recovery_id_byte = recid.to_i32() as u8; // recovery ID will be 0, 1, 2, or 3
        ret_bytes[0] = recovery_id_byte;
        ret_bytes[1..=64].copy_from_slice(&bytes[..64]);
        MessageSignature(ret_bytes)
    }

    pub fn to_secp256k1_recoverable(&self) -> Option<LibSecp256k1RecoverableSignature> {
        let recid = match LibSecp256k1RecoveryID::from_i32(self.0[0] as i32) {
            Ok(rid) => rid,
            Err(_) => {
                return None;
            }
        };
        let mut sig_bytes = [0u8; 64];
        sig_bytes[..64].copy_from_slice(&self.0[1..=64]);

        match LibSecp256k1RecoverableSignature::from_compact(&sig_bytes, recid) {
            Ok(sig) => Some(sig),
            Err(_) => None,
        }
    }

    /// Convert from VRS to RSV
    pub fn to_rsv(&self) -> Vec<u8> {
        [&self.0[1..], &self.0[0..1]].concat()
    }
}

#[cfg(any(test, feature = "testing"))]
impl Default for Secp256k1PublicKey {
    fn default() -> Self {
        Self::new()
    }
}

impl Secp256k1PublicKey {
    #[cfg(any(test, feature = "testing"))]
    pub fn new() -> Secp256k1PublicKey {
        Secp256k1PublicKey::from_private(&Secp256k1PrivateKey::new())
    }

    pub fn from_hex(hex_string: &str) -> Result<Secp256k1PublicKey, &'static str> {
        let data = hex_bytes(hex_string).map_err(|_e| "Failed to decode hex public key")?;
        Secp256k1PublicKey::from_slice(&data[..]).map_err(|_e| "Invalid public key hex string")
    }

    pub fn from_slice(data: &[u8]) -> Result<Secp256k1PublicKey, &'static str> {
        match LibSecp256k1PublicKey::from_slice(data) {
            Ok(pubkey_res) => Ok(Secp256k1PublicKey {
                key: pubkey_res,
                compressed: data.len() == LibSecp256k1Constants::PUBLIC_KEY_SIZE,
            }),
            Err(_e) => Err("Invalid public key: failed to load"),
        }
    }

    pub fn from_private(privk: &Secp256k1PrivateKey) -> Secp256k1PublicKey {
        _secp256k1.with(|ctx| {
            let pubk = LibSecp256k1PublicKey::from_secret_key(ctx, &privk.key);
            Secp256k1PublicKey {
                key: pubk,
                compressed: privk.compress_public,
            }
        })
    }

    pub fn to_hex(&self) -> String {
        to_hex(&self.to_bytes())
    }

    pub fn to_bytes_compressed(&self) -> Vec<u8> {
        self.key.serialize().to_vec()
    }

    pub fn compressed(&self) -> bool {
        self.compressed
    }

    pub fn set_compressed(&mut self, value: bool) {
        self.compressed = value;
    }

    /// recover message and signature to public key (will be compressed)
    pub fn recover_to_pubkey(
        msg: &[u8],
        sig: &MessageSignature,
    ) -> Result<Secp256k1PublicKey, &'static str> {
        _secp256k1.with(|ctx| {
            let msg = LibSecp256k1Message::from_slice(msg).map_err(|_e| {
                "Invalid message: failed to decode data hash: must be a 32-byte hash"
            })?;

            let secp256k1_sig = sig
                .to_secp256k1_recoverable()
                .ok_or("Invalid signature: failed to decode recoverable signature")?;

            let recovered_pubkey = ctx
                .recover_ecdsa(&msg, &secp256k1_sig)
                .map_err(|_e| "Invalid signature: failed to recover public key")?;

            Ok(Secp256k1PublicKey {
                key: recovered_pubkey,
                compressed: true,
            })
        })
    }

    // for benchmarking
    #[cfg(test)]
    pub fn recover_benchmark(
        msg: &LibSecp256k1Message,
        sig: &LibSecp256k1RecoverableSignature,
    ) -> Result<LibSecp256k1PublicKey, &'static str> {
        _secp256k1.with(|ctx| {
            ctx.recover_ecdsa(msg, sig)
                .map_err(|_e| "Invalid signature: failed to recover public key")
        })
    }
}

impl PublicKey for Secp256k1PublicKey {
    fn to_bytes(&self) -> Vec<u8> {
        if self.compressed {
            self.key.serialize().to_vec()
        } else {
            self.key.serialize_uncompressed().to_vec()
        }
    }

    fn verify(&self, data_hash: &[u8], sig: &MessageSignature) -> Result<bool, &'static str> {
        _secp256k1.with(|ctx| {
            let msg = LibSecp256k1Message::from_slice(data_hash).map_err(|_e| {
                "Invalid message: failed to decode data hash: must be a 32-byte hash"
            })?;

            let secp256k1_sig = sig
                .to_secp256k1_recoverable()
                .ok_or("Invalid signature: failed to decode recoverable signature")?;

            let recovered_pubkey = ctx
                .recover_ecdsa(&msg, &secp256k1_sig)
                .map_err(|_e| "Invalid signature: failed to recover public key")?;

            if recovered_pubkey != self.key {
                test_debug!("{:?} != {:?}", &recovered_pubkey, &self.key);
                return Ok(false);
            }

            // NOTE: libsecp256k1 _should_ ensure that the S is low,
            // but add this check just to be safe.
            let secp256k1_sig_standard = secp256k1_sig.to_standard();

            // must be low-S
            let mut secp256k1_sig_low_s = secp256k1_sig_standard;
            secp256k1_sig_low_s.normalize_s();
            if secp256k1_sig_low_s != secp256k1_sig_standard {
                return Err("Invalid signature: high-S");
            }

            Ok(true)
        })
    }
}

impl Default for Secp256k1PrivateKey {
    fn default() -> Self {
        Self::new()
    }
}

impl Secp256k1PrivateKey {
    pub fn new() -> Secp256k1PrivateKey {
        let mut rng = rand::thread_rng();
        loop {
            // keep trying to generate valid bytes
            let mut random_32_bytes = [0u8; 32];
            rng.fill_bytes(&mut random_32_bytes);
            let pk_res = LibSecp256k1PrivateKey::from_slice(&random_32_bytes);
            match pk_res {
                Ok(pk) => {
                    return Secp256k1PrivateKey {
                        key: pk,
                        compress_public: true,
                    };
                }
                Err(_) => {
                    continue;
                }
            }
        }
    }

    /// Create a Secp256k1PrivateKey from seed bytes by repeatedly
    ///  SHA256 hashing the seed bytes until a private key is found.
    ///
    /// If `seed` is a valid private key, it will be returned without hashing.
    /// The returned private key's compress_public flag will be `true`
    pub fn from_seed(seed: &[u8]) -> Secp256k1PrivateKey {
        let mut re_hashed_seed = Vec::from(seed);
        loop {
            if let Ok(mut sk) = Secp256k1PrivateKey::from_slice(&re_hashed_seed[..]) {
                // set this to true: LocalPeer will be doing this anyways,
                //  and that's currently the only way this method is used
                sk.set_compress_public(true);
                return sk;
            } else {
                re_hashed_seed = Sha256Sum::from_data(&re_hashed_seed[..])
                    .as_bytes()
                    .to_vec()
            }
        }
    }

    pub fn from_hex(hex_string: &str) -> Result<Secp256k1PrivateKey, &'static str> {
        let data = hex_bytes(hex_string).map_err(|_e| "Failed to decode hex private key")?;
        Secp256k1PrivateKey::from_slice(&data[..]).map_err(|_e| "Invalid private key hex string")
    }

    pub fn from_slice(data: &[u8]) -> Result<Secp256k1PrivateKey, &'static str> {
        if data.len() < 32 {
            return Err("Invalid private key: shorter than 32 bytes");
        }
        if data.len() > 33 {
            return Err("Invalid private key: greater than 33 bytes");
        }
        let compress_public = if data.len() == 33 {
            // compressed byte tag?
            if data[32] != 0x01 {
                return Err("Invalid private key: invalid compressed byte marker");
            }
            true
        } else {
            false
        };
        match LibSecp256k1PrivateKey::from_slice(&data[0..32]) {
            Ok(privkey_res) => Ok(Secp256k1PrivateKey {
                key: privkey_res,
                compress_public,
            }),
            Err(_e) => Err("Invalid private key: failed to load"),
        }
    }

    pub fn compress_public(&self) -> bool {
        self.compress_public
    }

    pub fn set_compress_public(&mut self, value: bool) {
        self.compress_public = value;
    }

    pub fn to_hex(&self) -> String {
        let mut bytes = self.key[..].to_vec();
        if self.compress_public {
            bytes.push(1);
        }
        to_hex(&bytes)
    }

    pub fn as_slice(&self) -> &[u8; 32] {
        self.key.as_ref()
    }
}

impl PrivateKey for Secp256k1PrivateKey {
    fn to_bytes(&self) -> Vec<u8> {
        let mut bits = self.key[..].to_vec();
        if self.compress_public {
            bits.push(0x01);
        }
        bits
    }

    fn sign(&self, data_hash: &[u8]) -> Result<MessageSignature, &'static str> {
        _secp256k1.with(|ctx| {
            let msg = LibSecp256k1Message::from_slice(data_hash).map_err(|_e| {
                "Invalid message: failed to decode data hash: must be a 32-byte hash"
            })?;

            let sig = ctx.sign_ecdsa_recoverable(&msg, &self.key);
            Ok(MessageSignature::from_secp256k1_recoverable(&sig))
        })
    }
}

fn secp256k1_pubkey_serialize<S: serde::Serializer>(
    pubk: &LibSecp256k1PublicKey,
    s: S,
) -> Result<S::Ok, S::Error> {
    let key_hex = to_hex(&pubk.serialize());
    s.serialize_str(key_hex.as_str())
}

fn secp256k1_pubkey_deserialize<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<LibSecp256k1PublicKey, D::Error> {
    let key_hex = String::deserialize(d)?;
    let key_bytes = hex_bytes(&key_hex).map_err(de_Error::custom)?;

    LibSecp256k1PublicKey::from_slice(&key_bytes).map_err(de_Error::custom)
}

fn secp256k1_privkey_serialize<S: serde::Serializer>(
    privk: &LibSecp256k1PrivateKey,
    s: S,
) -> Result<S::Ok, S::Error> {
    let key_hex = to_hex(&privk[..]);
    s.serialize_str(key_hex.as_str())
}

fn secp256k1_privkey_deserialize<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<LibSecp256k1PrivateKey, D::Error> {
    let key_hex = String::deserialize(d)?;
    let key_bytes = hex_bytes(&key_hex).map_err(de_Error::custom)?;

    LibSecp256k1PrivateKey::from_slice(&key_bytes[..]).map_err(de_Error::custom)
}

pub fn secp256k1_recover(
    message_arr: &[u8],
    serialized_signature_arr: &[u8],
) -> Result<[u8; 33], LibSecp256k1Error> {
    _secp256k1.with(|ctx| {
        let message = LibSecp256k1Message::from_slice(message_arr)?;

        let rec_id = LibSecp256k1RecoveryID::from_i32(serialized_signature_arr[64] as i32)?;
        let recovered_sig = LibSecp256k1RecoverableSignature::from_compact(
            &serialized_signature_arr[..64],
            rec_id,
        )?;
        let recovered_pub = ctx.recover_ecdsa(&message, &recovered_sig)?;
        let recovered_serialized = recovered_pub.serialize(); // 33 bytes version

        Ok(recovered_serialized)
    })
}

pub fn secp256k1_verify(
    message_arr: &[u8],
    serialized_signature_arr: &[u8],
    pubkey_arr: &[u8],
) -> Result<(), LibSecp256k1Error> {
    _secp256k1.with(|ctx| {
        let message = LibSecp256k1Message::from_slice(message_arr)?;
        let expanded_sig = LibSecp256k1Signature::from_compact(&serialized_signature_arr[..64])?; // ignore 65th byte if present
        let pubkey = LibSecp256k1PublicKey::from_slice(pubkey_arr)?;
        ctx.verify_ecdsa(&message, &expanded_sig, &pubkey)
    })
}

#[cfg(test)]
mod tests {
    use secp256k1;
    use secp256k1::{PublicKey as LibSecp256k1PublicKey, Secp256k1};

    use super::*;
    use crate::util::hash::hex_bytes;
    use crate::util::{get_epoch_time_ms, log};

    struct KeyFixture<I, R> {
        input: I,
        result: R,
    }

    #[derive(Debug)]
    struct VerifyFixture<R> {
        public_key: &'static str,
        data: &'static str,
        signature: &'static str,
        result: R,
    }

    #[test]
    fn test_parse_serialize_compressed() {
        let mut t1 = Secp256k1PrivateKey::new();
        t1.set_compress_public(true);
        let h_comp = t1.to_hex();
        t1.set_compress_public(false);
        let h_uncomp = t1.to_hex();

        assert!(h_comp != h_uncomp);
        assert_eq!(h_comp.len(), 66);
        assert_eq!(h_uncomp.len(), 64);

        let (uncomp, comp_value) = h_comp.split_at(64);
        assert_eq!(comp_value, "01");
        assert_eq!(uncomp, &h_uncomp);

        assert!(Secp256k1PrivateKey::from_hex(&h_comp)
            .unwrap()
            .compress_public());
        assert!(!Secp256k1PrivateKey::from_hex(&h_uncomp)
            .unwrap()
            .compress_public());

        assert_eq!(Secp256k1PrivateKey::from_hex(&h_uncomp), Ok(t1));

        t1.set_compress_public(true);

        assert_eq!(Secp256k1PrivateKey::from_hex(&h_comp), Ok(t1));
    }

    #[test]
    /// Test the behavior of from_seed using hard-coded values from previous existing integration tests
    fn sk_from_seed() {
        let sk = Secp256k1PrivateKey::from_seed(&[2; 32]);
        assert_eq!(
            Secp256k1PublicKey::from_private(&sk).to_hex(),
            "024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766"
        );
        assert_eq!(
            sk.to_hex(),
            "020202020202020202020202020202020202020202020202020202020202020201"
        );

        let sk = Secp256k1PrivateKey::from_seed(&[0]);
        assert_eq!(
            Secp256k1PublicKey::from_private(&sk).to_hex(),
            "0243311589af63c2adda04fcd7792c038a05c12a4fe40351b3eb1612ff6b2e5a0e"
        );
        assert_eq!(
            sk.to_hex(),
            "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d01"
        );
    }

    #[test]
    fn test_parse_serialize() {
        let ctx: Secp256k1<secp256k1::All> = Secp256k1::new();
        let fixtures = vec![
            KeyFixture {
                input: "0233d78f74de8ef4a1de815b6d5c5c129c073786305c0826c499b1811c9a12cee5",
                result: Some(Secp256k1PublicKey {
                    key: LibSecp256k1PublicKey::from_slice(&hex_bytes("0233d78f74de8ef4a1de815b6d5c5c129c073786305c0826c499b1811c9a12cee5").unwrap()[..]).unwrap(),
                    compressed: true
                })
            },
            KeyFixture {
                input: "044a83ad59dbae1e2335f488dbba5f8604d00f612a43ebaae784b5b7124cc38c3aaf509362787e1a8e25131724d57fec81b87889aabb4edf7bd89f5c4daa4f8aa7",
                result: Some(Secp256k1PublicKey {
                    key: LibSecp256k1PublicKey::from_slice(&hex_bytes("044a83ad59dbae1e2335f488dbba5f8604d00f612a43ebaae784b5b7124cc38c3aaf509362787e1a8e25131724d57fec81b87889aabb4edf7bd89f5c4daa4f8aa7").unwrap()[..]).unwrap(),
                    compressed: false
                })
            },
            KeyFixture {
                input: "0233d78f74de8ef4a1de815b6d5c5c129c073786305c0826c499b1811c9a12ce",
                result: None,
            },
            KeyFixture {
                input: "044a83ad59dbae1e2335f488dbba5f8604d00f612a43ebaae784b5b7124cc38c3aaf509362787e1a8e25131724d57fec81b87889aabb4edf7bd89f5c4daa4f8a",
                result: None,
            }
        ];

        for fixture in fixtures {
            let key_res = Secp256k1PublicKey::from_hex(fixture.input);
            match (key_res, fixture.result) {
                (Ok(key), Some(key_result)) => {
                    assert_eq!(key, key_result);

                    let key_from_slice =
                        Secp256k1PublicKey::from_slice(&hex_bytes(fixture.input).unwrap()[..])
                            .unwrap();
                    assert_eq!(key_from_slice, key_result);

                    let key_bytes = key.to_bytes();
                    assert_eq!(key_bytes, hex_bytes(fixture.input).unwrap());
                }
                (Err(_e), None) => {}
                (_, _) => {
                    // either got a key when we didn't expect one, or didn't get a key when we did
                    // expect one.
                    assert!(false, "Unexpected result: we either got a key when we didn't expect one, or didn't get a key when we did expect one.");
                }
            }
        }
    }

    #[test]
    fn test_verify() {
        let _ctx: Secp256k1<secp256k1::All> = Secp256k1::new();
        let fixtures : Vec<VerifyFixture<Result<bool, &'static str>>> = vec![
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "00354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Ok(true)
            },
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "00354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",
                data: "ca3704aa0b06f5954c79ee837faa152d84d6b2d42838f0637a15eda8337dbdce",       // sha256 hash of "nope"
                result: Ok(false)
            },
            VerifyFixture {
                public_key: "034c35b09b758678165d6ed84a50b329900c99986cf8e9a358ceae0d03af91f5b6",   // wrong key
                signature: "00354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Ok(false)
            },
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "00354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe7",  // wrong sig (bad s)
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Ok(false)
            },
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "00454445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",  // wrong sig (bad r)
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Ok(false)
            },
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "01354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",  // wrong sig (bad recovery)
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Ok(false)
            },
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "02354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",  // wrong sig (bad recovery)
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Err("Invalid signature: failed to recover public key"),
            },
            VerifyFixture {
                public_key: "0385f2e2867524289d6047d0d9c5e764c5d413729fc32291ad2c353fbc396a4219",
                signature: "03354445a1dc98a1bd27984dbe69979a5cd77886b4d9134af5c40e634d96e1cb445b97de5b632582d31704f86706a780886e6e381bfed65228267358262d203fe6",  // wrong sig (bad recovery)
                data: "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9",       // sha256 hash of "hello world"
                result: Err("Invalid signature: failed to recover public key"),
            }
        ];

        for fixture in fixtures {
            let key = Secp256k1PublicKey::from_hex(fixture.public_key).unwrap();
            let signature = MessageSignature::from_raw(&hex_bytes(fixture.signature).unwrap());
            let ver_res = key.verify(&hex_bytes(fixture.data).unwrap(), &signature);
            match (ver_res, fixture.result) {
                (Ok(true), Ok(true)) => {}
                (Ok(false), Ok(false)) => {}
                (Err(e1), Err(e2)) => assert_eq!(e1, e2),
                (Err(e1), _) => {
                    test_debug!("Failed to verify signature: {}", e1);
                    assert!(
                        false,
                        "failed fixture (verification: {:?}): {:#?}",
                        &ver_res, &fixture
                    );
                }
                (_, _) => {
                    assert!(
                        false,
                        "failed fixture (verification: {:?}): {:#?}",
                        &ver_res, &fixture
                    );
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn test_verify_benchmark_roundtrip() {
        let mut runtime_sign = 0;
        let mut runtime_verify = 0;
        let mut runtime_recover = 0;
        let mut rng = rand::thread_rng();

        for i in 0..100 {
            let privk = Secp256k1PrivateKey::new();
            let pubk = Secp256k1PublicKey::from_private(&privk);

            let mut msg = [0u8; 32];
            rng.fill_bytes(&mut msg);

            let sign_start = get_epoch_time_ms();
            for i in 0..1000 {
                let sig = privk.sign(&msg).unwrap();
            }
            let sign_end = get_epoch_time_ms();

            let sig = privk.sign(&msg).unwrap();
            let secp256k1_msg = LibSecp256k1Message::from_slice(&msg).unwrap();
            let secp256k1_sig = sig.to_secp256k1_recoverable().unwrap();

            let recovered_pubk =
                Secp256k1PublicKey::recover_benchmark(&secp256k1_msg, &secp256k1_sig).unwrap();
            assert_eq!(recovered_pubk, pubk.key);

            let recover_start = get_epoch_time_ms();
            for i in 0..1000 {
                let recovered_pubk =
                    Secp256k1PublicKey::recover_benchmark(&secp256k1_msg, &secp256k1_sig).unwrap();
            }
            let recover_end = get_epoch_time_ms();

            let verify_start = get_epoch_time_ms();
            for i in 0..1000 {
                let valid = pubk.verify(&msg, &sig).unwrap();
            }
            let verify_end = get_epoch_time_ms();

            let valid = pubk.verify(&msg, &sig).unwrap();
            assert!(valid);

            test_debug!(
                "Runtime: {:?} sign, {:?} recover, {:?} verify",
                ((sign_end - sign_start) as f64) / 1000.0,
                ((recover_end - recover_start) as f64) / 1000.0,
                ((verify_end - verify_start) as f64) / 1000.0
            );

            runtime_sign += sign_end - sign_start;
            runtime_verify += verify_end - verify_start;
            runtime_recover += recover_end - recover_start;
        }

        test_debug!(
            "Total Runtime: {:?} sign, {:?} verify, {:?} recover, {:?} verify - recover",
            runtime_sign,
            runtime_verify,
            runtime_recover,
            runtime_verify - runtime_recover
        );
    }
}
