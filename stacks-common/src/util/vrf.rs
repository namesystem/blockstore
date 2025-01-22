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

#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::io::{Read, Write};
/// This codebase is based on routines defined in the IETF draft for verifiable random functions
/// over elliptic curves (https://tools.ietf.org/id/draft-irtf-cfrg-vrf-02.html).
use std::ops::Deref;
use std::ops::DerefMut;
use std::{error, fmt};

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::scalar::Scalar as ed25519_Scalar;
use ed25519_dalek::{
    SecretKey as EdDalekSecretKeyBytes, SigningKey as EdPrivateKey, VerifyingKey as EdPublicKey,
};
use rand;
use sha2::{Digest, Sha512};

use super::hash::Sha512Trunc256Sum;
use crate::codec::{Error as CodecError, StacksMessageCodec};
use crate::types::chainstate::VRFSeed;
use crate::util::hash::{hex_bytes, to_hex};

#[derive(Clone)]
pub struct VRFPublicKey(pub ed25519_dalek::VerifyingKey);

#[derive(Clone)]
pub struct VRFPrivateKey(pub ed25519_dalek::SigningKey);

impl serde::Serialize for VRFPublicKey {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let inst = self.to_hex();
        s.serialize_str(inst.as_str())
    }
}

impl<'de> serde::Deserialize<'de> for VRFPublicKey {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<VRFPublicKey, D::Error> {
        let inst_str = String::deserialize(d)?;
        VRFPublicKey::from_hex(&inst_str)
            .ok_or_else(|| serde::de::Error::custom("Failed to parse VRF Public Key from hex"))
    }
}

impl Debug for VRFPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.to_hex())
    }
}

impl PartialEq for VRFPublicKey {
    fn eq(&self, other: &VRFPublicKey) -> bool {
        self.as_bytes().to_vec() == other.as_bytes().to_vec()
    }
}

impl Eq for VRFPublicKey {}

impl PartialOrd for VRFPublicKey {
    fn partial_cmp(&self, other: &VRFPublicKey) -> Option<Ordering> {
        Some(self.as_bytes().to_vec().cmp(&other.as_bytes().to_vec()))
    }
}

impl Ord for VRFPublicKey {
    fn cmp(&self, other: &VRFPublicKey) -> Ordering {
        self.as_bytes().to_vec().cmp(&other.as_bytes().to_vec())
    }
}

impl Hash for VRFPublicKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}

impl Debug for VRFPrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.to_hex())
    }
}

// do NOT ship this comparison code in production -- it's NOT constant-time
#[cfg(test)]
impl PartialEq for VRFPrivateKey {
    fn eq(&self, other: &VRFPrivateKey) -> bool {
        self.as_bytes().to_vec() == other.as_bytes().to_vec()
    }
}

impl Default for VRFPrivateKey {
    fn default() -> Self {
        Self::new()
    }
}

impl VRFPrivateKey {
    pub fn new() -> VRFPrivateKey {
        let mut rng = rand::thread_rng();
        let signing_key = ed25519_dalek::SigningKey::generate(&mut rng);
        VRFPrivateKey(signing_key)
    }

    pub fn from_hex(h: &str) -> Option<VRFPrivateKey> {
        let bytes = hex_bytes(h).ok()?;
        Self::from_bytes(bytes.as_slice())
    }

    pub fn from_bytes(b: &[u8]) -> Option<VRFPrivateKey> {
        let signing_key = ed25519_dalek::SigningKey::try_from(b).ok()?;
        Some(VRFPrivateKey(signing_key))
    }

    pub fn to_hex(&self) -> String {
        to_hex(self.as_bytes())
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }
}

impl VRFPublicKey {
    pub fn from_private(sk: &VRFPrivateKey) -> VRFPublicKey {
        VRFPublicKey(sk.0.verifying_key())
    }

    /// Verify that a given byte string is a well-formed EdDSA public
    /// key (i.e. it's a compressed Edwards point that is valid), and return
    /// a VRFPublicKey if so
    pub fn from_bytes(pubkey_bytes: &[u8]) -> Option<VRFPublicKey> {
        let pubkey_slice = pubkey_bytes.try_into().ok()?;

        // NOTE: `ed25519_dalek::VerifyingKey::from_bytes` docs say
        //  that this check must be performed by the caller, but as of
        //  latest, it actually performs the check as well. However,
        //  we do this check out of an abundance of caution because
        //  that's what the docs say to do!

        let checked_pubkey = CompressedEdwardsY(pubkey_slice);
        checked_pubkey.decompress()?;

        let key = ed25519_dalek::VerifyingKey::from_bytes(&pubkey_slice).ok()?;
        Some(VRFPublicKey(key))
    }

    pub fn from_hex(h: &str) -> Option<VRFPublicKey> {
        let bytes = hex_bytes(h).ok()?;
        Self::from_bytes(bytes.as_slice())
    }

    pub fn to_hex(&self) -> String {
        to_hex(self.as_bytes())
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }
}

#[derive(Debug)]
pub enum Error {
    InvalidPublicKey,
    InvalidDataError,
    OSRNGError(rand::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::InvalidPublicKey => write!(f, "Invalid public key"),
            Error::InvalidDataError => write!(f, "No data could be found"),
            Error::OSRNGError(ref e) => fmt::Display::fmt(e, f),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Error::InvalidPublicKey => None,
            Error::InvalidDataError => None,
            Error::OSRNGError(ref e) => Some(e),
        }
    }
}

pub const SUITE: u8 = 0x03;

#[derive(Clone, PartialEq, Eq)]
pub struct VRFProof {
    // force private so we don't accidentally expose
    // an invalid c point
    // Gamma: RistrettoPoint,
    Gamma: EdwardsPoint,
    c: ed25519_Scalar,
    s: ed25519_Scalar,
}

impl Debug for VRFProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.to_hex())
    }
}

impl Hash for VRFProof {
    fn hash<H: Hasher>(&self, h: &mut H) {
        let bytes = self.to_bytes();
        bytes.hash(h);
    }
}

pub const VRF_PROOF_ENCODED_SIZE: u32 = 80;

impl VRFProof {
    pub fn Gamma(&self) -> &EdwardsPoint {
        &self.Gamma
    }

    pub fn s(&self) -> &ed25519_Scalar {
        &self.s
    }

    pub fn c(&self) -> &ed25519_Scalar {
        &self.c
    }

    #[allow(clippy::needless_range_loop)]
    pub fn check_c(c: &ed25519_Scalar) -> bool {
        let c_bytes = c.reduce().to_bytes();

        // upper 16 bytes of c must be 0's
        for c_byte in c_bytes[16..32].iter() {
            if *c_byte != 0 {
                return false;
            }
        }
        true
    }

    pub fn empty() -> VRFProof {
        // can't be all 0's, since an all-0 string decodes to a low-order point
        VRFProof::from_slice(&[1u8; 80]).unwrap()
    }

    pub fn new(
        Gamma: EdwardsPoint,
        c: ed25519_Scalar,
        s: ed25519_Scalar,
    ) -> Result<VRFProof, Error> {
        if !VRFProof::check_c(&c) {
            return Err(Error::InvalidDataError);
        }

        Ok(VRFProof { Gamma, c, s })
    }

    pub fn from_slice(bytes: &[u8]) -> Option<VRFProof> {
        match bytes.len() {
            80 => {
                // format:
                // 0                            32         48                         80
                // |----------------------------|----------|---------------------------|
                //      Gamma point               c scalar   s scalar
                let gamma_opt = CompressedEdwardsY::from_slice(&bytes[0..32]).decompress();
                if gamma_opt.is_none() {
                    test_debug!("Invalid Gamma");
                    return None;
                }
                let gamma = gamma_opt.unwrap();
                if gamma.is_small_order() {
                    test_debug!("Invalid Gamma -- small order");
                    return None;
                }

                let mut c_buf = [0u8; 32];
                let mut s_buf = [0u8; 32];

                c_buf[..16].copy_from_slice(&bytes[32..(16 + 32)]);
                s_buf[..32].copy_from_slice(&bytes[48..(32 + 48)]);
                let c = ed25519_Scalar::from_canonical_bytes(c_buf)?;
                let s = ed25519_Scalar::from_canonical_bytes(s_buf)?;

                Some(VRFProof { Gamma: gamma, c, s })
            }
            _ => None,
        }
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<VRFProof> {
        VRFProof::from_slice(bytes)
    }

    pub fn from_hex(hex_str: &str) -> Option<VRFProof> {
        match hex_bytes(hex_str) {
            Ok(b) => VRFProof::from_slice(&b[..]),
            Err(_) => None,
        }
    }

    pub fn to_bytes(&self) -> [u8; 80] {
        let mut c_bytes_16 = [0u8; 16];
        assert!(
            VRFProof::check_c(&self.c),
            "FATAL ERROR: somehow constructed an invalid ECVRF proof"
        );

        let c_bytes = self.c.reduce().to_bytes();
        c_bytes_16[0..16].copy_from_slice(&c_bytes[0..16]);

        let gamma_bytes = self.Gamma.compress().to_bytes();
        let s_bytes = self.s.to_bytes();

        let mut ret: Vec<u8> = Vec::with_capacity(80);
        ret.extend_from_slice(&gamma_bytes);
        ret.extend_from_slice(&c_bytes_16);
        ret.extend_from_slice(&s_bytes);

        let mut proof_bytes = [0u8; 80];
        proof_bytes.copy_from_slice(&ret[..]);
        proof_bytes
    }

    pub fn to_hex(&self) -> String {
        to_hex(&self.to_bytes())
    }
}

impl serde::Serialize for VRFProof {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let inst = self.to_hex();
        s.serialize_str(&inst)
    }
}

impl<'de> serde::Deserialize<'de> for VRFProof {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<VRFProof, D::Error> {
        let inst_str = String::deserialize(d)?;
        VRFProof::from_hex(&inst_str).ok_or(serde::de::Error::custom(Error::InvalidDataError))
    }
}

pub struct VRF {}

impl VRF {
    /// Hash-to-curve, Try-and-increment approach (described in
    /// https://tools.ietf.org/id/draft-irtf-cfrg-vrf-02.html)
    fn hash_to_curve(y: &VRFPublicKey, alpha: &[u8]) -> EdwardsPoint {
        let mut ctr: u64 = 0;

        let h: EdwardsPoint = loop {
            let mut hasher = Sha512::new();
            hasher.update([SUITE, 0x01]);
            hasher.update(y.as_bytes());
            hasher.update(alpha);

            if ctr == 0 {
                hasher.update([0u8]);
            } else {
                // 2**64 - 1 is an artificial cap -- the RFC implies that you should count forever
                let ctr_bytes = ctr.to_le_bytes();
                for (i, ctr_byte) in ctr_bytes.iter().enumerate() {
                    if ctr > 1u64 << (8 * i) {
                        hasher.update([*ctr_byte]);
                    }
                }
            }

            let y = CompressedEdwardsY::from_slice(&hasher.finalize()[0..32]);
            if let Some(h) = y.decompress() {
                break h;
            }

            ctr = ctr
                .checked_add(1)
                .expect("Too many attempts at try-and-increment hash-to-curve");
        };

        h.mul_by_cofactor()
    }

    /// Hash four points to a 16-byte string.
    /// Implementation of https://tools.ietf.org/id/draft-irtf-cfrg-vrf-02.html#rfc.section.5.4.2
    fn hash_points(
        p1: &EdwardsPoint,
        p2: &EdwardsPoint,
        p3: &EdwardsPoint,
        p4: &EdwardsPoint,
    ) -> [u8; 16] {
        let mut hasher = Sha512::new();
        let mut hash128 = [0u8; 16];

        // hasher.input(&[SUITE, 0x02]);
        hasher.update([0x03, 0x02]);
        hasher.update(p1.compress().to_bytes());
        hasher.update(p2.compress().to_bytes());
        hasher.update(p3.compress().to_bytes());
        hasher.update(p4.compress().to_bytes());

        hash128.copy_from_slice(&hasher.finalize()[0..16]);
        hash128
    }

    /// Auxilliary function to convert an ed25519 private key into:
    /// * its public key (an ed25519 curve point)
    /// * a new private key derived from the hash of the private key
    /// * a truncated hash of the private key
    ///   Idea borrowed from Algorand (https://github.com/algorand/libsodium/blob/draft-irtf-cfrg-vrf-03/src/libsodium/crypto_vrf/ietfdraft03/prove.c)
    fn expand_privkey(secret: &VRFPrivateKey) -> (VRFPublicKey, ed25519_Scalar, [u8; 32]) {
        let mut hasher = Sha512::new();
        let mut h = [0u8; 64];
        let mut trunc_hash = [0u8; 32];
        let pubkey = VRFPublicKey::from_private(secret);
        let privkey_buf = secret.to_bytes();

        // hash secret key to produce nonce and intermediate private key
        hasher.update(&privkey_buf[0..32]);
        h.copy_from_slice(&hasher.finalize()[..]);

        // h[0..32] will encode a new private key, so we need to twiddle a few bits to make sure it falls in the
        // right range (i.e. the curve order).
        h[0] &= 248;
        h[31] &= 127;
        h[31] |= 64;

        let mut h_32 = [0u8; 32];
        h_32.copy_from_slice(&h[0..32]);

        let x_scalar_raw = ed25519_Scalar::from_bits(h_32);
        let x_scalar = x_scalar_raw.reduce(); // use the canonical scalar for the private key

        trunc_hash.copy_from_slice(&h[32..64]);

        (pubkey, x_scalar, trunc_hash)
    }

    /// RFC8032 nonce generation for ed25519, given part of a hash of a private key and a public key
    fn nonce_generation(trunc_hash: &[u8; 32], H_point: &EdwardsPoint) -> ed25519_Scalar {
        let mut hasher = Sha512::new();
        let mut k_string = [0u8; 64];
        let h_string = H_point.compress().to_bytes();

        hasher.update(trunc_hash);
        hasher.update(h_string);
        let rs = &hasher.finalize()[..];
        k_string.copy_from_slice(rs);

        ed25519_Scalar::from_bytes_mod_order_wide(&k_string)
    }

    /// Convert a 16-byte string into a scalar.
    /// The upper 16 bytes in the resulting scalar MUST BE 0's
    fn ed25519_scalar_from_hash128(hash128: &[u8; 16]) -> ed25519_Scalar {
        let mut scalar_buf = [0u8; 32];
        scalar_buf[0..16].copy_from_slice(hash128);

        ed25519_Scalar::from_bits(scalar_buf)
    }

    /// ECVRF proof routine
    /// https://tools.ietf.org/id/draft-irtf-cfrg-vrf-02.html#rfc.section.5.1
    #[allow(clippy::op_ref)]
    pub fn prove(secret: &VRFPrivateKey, alpha: &[u8]) -> VRFProof {
        let (Y_point, x_scalar, trunc_hash) = VRF::expand_privkey(secret);
        let H_point = VRF::hash_to_curve(&Y_point, alpha);

        let Gamma_point = &x_scalar * &H_point;
        let k_scalar = VRF::nonce_generation(&trunc_hash, &H_point);

        let kB_point = &k_scalar * &ED25519_BASEPOINT_POINT;
        let kH_point = &k_scalar * &H_point;

        let c_hashbuf = VRF::hash_points(&H_point, &Gamma_point, &kB_point, &kH_point);
        let c_scalar = VRF::ed25519_scalar_from_hash128(&c_hashbuf);

        let s_full_scalar = &k_scalar + &c_scalar * &x_scalar;
        let s_scalar = s_full_scalar.reduce();

        // NOTE: expect() won't panic because c_scalar is guaranteed to have
        // its upper 16 bytes as 0
        VRFProof::new(Gamma_point, c_scalar, s_scalar)
            .expect("FATAL ERROR: upper-16 bytes of proof's C scalar are NOT 0")
    }

    /// Given a public key, verify that the private key owner that generate the ECVRF proof did so on the given message.
    /// Return Ok(true) if so
    /// Return Ok(false) if not
    /// Return Err(Error) if the public key is invalid, or we are unable to do one of the
    /// necessary internal data conversions.
    #[allow(clippy::op_ref)]
    pub fn verify(Y_point: &VRFPublicKey, proof: &VRFProof, alpha: &[u8]) -> Result<bool, Error> {
        let H_point = VRF::hash_to_curve(Y_point, alpha);
        let s_reduced = proof.s().reduce();
        let Y_point_ed = CompressedEdwardsY(Y_point.to_bytes())
            .decompress()
            .ok_or(Error::InvalidPublicKey)?;
        if proof.Gamma().is_small_order() {
            return Err(Error::InvalidPublicKey);
        }

        let U_point = &s_reduced * &ED25519_BASEPOINT_POINT - proof.c() * Y_point_ed;
        let V_point = &s_reduced * &H_point - proof.c() * proof.Gamma();

        let c_prime_hashbuf = VRF::hash_points(&H_point, proof.Gamma(), &U_point, &V_point);
        let c_prime = VRF::ed25519_scalar_from_hash128(&c_prime_hashbuf);

        // NOTE: this leverages constant-time comparison inherited from the Scalar impl
        Ok(c_prime == *(proof.c()))
    }
}

impl StacksMessageCodec for VRFProof {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        fd.write_all(&self.to_bytes())
            .map_err(CodecError::WriteError)
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<VRFProof, CodecError> {
        let mut bytes = [0u8; VRF_PROOF_ENCODED_SIZE as usize];
        fd.read_exact(&mut bytes).map_err(CodecError::ReadError)?;
        let res = VRFProof::from_slice(&bytes).ok_or(CodecError::DeserializeError(
            "Failed to parse VRF proof".to_string(),
        ))?;

        Ok(res)
    }
}

pub const VRF_SEED_ENCODED_SIZE: u32 = 32;

impl VRFSeed {
    /// First-ever VRF seed from the genesis block.  It's all 0's
    pub fn initial() -> VRFSeed {
        VRFSeed::from_hex("0000000000000000000000000000000000000000000000000000000000000000")
            .unwrap()
    }

    pub fn from_proof(proof: &VRFProof) -> VRFSeed {
        let h = Sha512Trunc256Sum::from_data(&proof.to_bytes());
        VRFSeed(h.0)
    }

    pub fn is_from_proof(&self, proof: &VRFProof) -> bool {
        self.as_bytes().to_vec() == VRFSeed::from_proof(proof).as_bytes().to_vec()
    }
}

#[cfg(test)]
mod tests {
    use curve25519_dalek::scalar::Scalar as ed25519_Scalar;
    use rand;
    use rand::RngCore;
    use sha2::Sha512;

    use super::*;
    use crate::util::hash::hex_bytes;

    #[derive(Debug)]
    struct VRF_Proof_Fixture {
        privkey: Vec<u8>,
        message: &'static str,
        proof: Vec<u8>,
    }

    #[derive(Debug)]
    struct VRF_Verify_Fixture {
        pubkey: Vec<u8>,
        proof: Vec<u8>,
        message: &'static str,
        result: bool,
    }

    #[derive(Debug)]
    struct VRF_Proof_Codec_Fixture {
        proof: Vec<u8>,
        result: bool,
    }

    // from Appendix A.3 in https://tools.ietf.org/id/draft-irtf-cfrg-vrf-04.html
    #[test]
    fn test_vrf_rfc() {
        let proof_fixtures = vec![
            VRF_Proof_Fixture {
                privkey: hex_bytes("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60").unwrap(),
                message: "",
                proof: hex_bytes("9275df67a68c8745c0ff97b48201ee6db447f7c93b23ae24cdc2400f52fdb08a1a6ac7ec71bf9c9c76e96ee4675ebff60625af28718501047bfd87b810c2d2139b73c23bd69de66360953a642c2a330a").unwrap()
            },
            VRF_Proof_Fixture {
                privkey: hex_bytes("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb").unwrap(),
                message: "72",
                proof: hex_bytes("84a63e74eca8fdd64e9972dcda1c6f33d03ce3cd4d333fd6cc789db12b5a7b9d03f1cb6b2bf7cd81a2a20bacf6e1c04e59f2fa16d9119c73a45a97194b504fb9a5c8cf37f6da85e03368d6882e511008").unwrap()
            },
            VRF_Proof_Fixture {
                privkey: hex_bytes("c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7").unwrap(),
                message: "af82",
                proof: hex_bytes("aca8ade9b7f03e2b149637629f95654c94fc9053c225ec21e5838f193af2b727b84ad849b0039ad38b41513fe5a66cdd2367737a84b488d62486bd2fb110b4801a46bfca770af98e059158ac563b690f").unwrap()
            }
        ];

        for proof_fixture in proof_fixtures {
            let alpha = hex_bytes(proof_fixture.message).unwrap();
            let privk = VRFPrivateKey::from_bytes(&proof_fixture.privkey[..]).unwrap();
            let expected_proof_bytes = &proof_fixture.proof[..];

            let proof = VRF::prove(&privk, &alpha.to_vec());
            let proof_bytes = proof.to_bytes();

            assert_eq!(proof_bytes.to_vec(), expected_proof_bytes.to_vec());

            let pubk = VRFPublicKey::from_private(&privk);
            let res = VRF::verify(&pubk, &proof, &alpha.to_vec()).unwrap();

            assert!(res);
        }
    }

    #[test]
    fn test_random_proof_roundtrip() {
        for _i in 0..100 {
            let secret_key = VRFPrivateKey::new();
            let public_key = VRFPublicKey::from_private(&secret_key);

            let mut rng = rand::thread_rng();
            let mut msg = [0u8; 1024];
            rng.fill_bytes(&mut msg);

            let proof = VRF::prove(&secret_key, &msg);
            let res = VRF::verify(&public_key, &proof, &msg).unwrap();

            assert!(res);
        }
    }

    #[test]
    fn test_proof_codec() {
        let proof_fixtures = vec![
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("ced9804ca06ed515c632fb83ef89e9cba4acf1539a33685a1c1cb475df733a5af33288af50fe1fa1c3facd9d19cf7ad98ba7413a8d09010363ac11ae7c4110b94707ab5bdee3726792daaf2c7f4f6106").unwrap(),
                result: true
            },
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("86bfdbd03147ae8bd3e16c76c9e40fe02e6fd2d7b072dce710897d97558fd00ec027222746d07207c381621b3a7d34db29762b43b73b6af816ca64da1503d37138fbb9e73faf82e83525be00f880cf04").unwrap(),
                result: true,
            },
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("6d5af6e8d02e4c04f7ee114c0adb7ff5ed2982e7b63cc0a82ec68c9a0967abfa07bbf70e92c03fcafb9a0a779cb511c85c946853154b406cb5a37563751886ac1f14d81694cf99fb103e712aa879c20f").unwrap(),
                result: true,
            },
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("ead84ef119fc0240395448853b0f1ca54e686c1fbbc0ed1669d24d95dcdd078f5273365211c6a7f66025e1114206ba8e721d0f486b952a544ab354cdc15ffa0957a0491f659be554de21d67cb86e880f").unwrap(),
                result: true,
            },
            // should fail -- 79 bytes
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("94654efaef05909d40ddd4e0bb8aae8fd70780b22bb57844fb4c1d81636ed6556d9725d59ccb0975b9c70b8cb2b20d781455e44d5914d15ed7eefdc58606b085ae13aa9c2e5d03c081e81fc25f945b").unwrap(),
                result: false,
            },
            // should fail -- 81 bytes
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("94654efaef05909d40ddd4e0bb8aae8fd70780b22bb57844fb4c1d81636ed6556d9725d59ccb0975b9c70b8cb2b20d781455e44d5914d15ed7eefdc58606b085ae13aa9c2e5d03c081e81fc25f945b0c01").unwrap(),
                result: false,
            },
            // should fail -- Gamma isn't a valid point
            VRF_Proof_Codec_Fixture {
                proof: hex_bytes("0000000000000000000000000000000000000000000000000000000000000000000025d59ccb0975b9c70b8cb2b20d781455e44d5914d15ed7eefdc58606b085ae13aa9c2e5d03c081e81fc25f945b0c").unwrap(),
                result: false,
            },
        ];

        for proof_fixture in proof_fixtures {
            let proof_res = VRFProof::from_bytes(&proof_fixture.proof);
            if proof_fixture.result {
                // should decode
                assert!(proof_res.is_some());

                // should re-encode
                assert!(proof_res.unwrap().to_bytes().to_vec() == proof_fixture.proof.to_vec());
            } else {
                assert!(proof_res.is_none());
            }
        }
    }

    #[test]
    fn check_valid_public_key() {
        let res1 = VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                .unwrap()
                .to_vec(),
        );
        assert!(res1.is_some());

        let res2 = VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7b")
                .unwrap()
                .to_vec(),
        );
        assert!(res2.is_none());
    }
}
