// Rust Bitcoin Library
// Written in 2014 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! Utility functions
//!
//! Functions needed by all parts of the Bitcoin library

pub mod hash;

use std::{error, fmt};

use crate::deps_common::bitcoin::network;
use crate::deps_common::bitcoin::network::serialize;
use crate::util::secp256k1::Error as Secp256k1Error;

/// A trait which allows numbers to act as fixed-size bit arrays
pub trait BitArray {
    /// Is bit set?
    fn bit(&self, idx: usize) -> bool;

    /// Returns an array which is just the bits from start to end
    fn bit_slice(&self, start: usize, end: usize) -> Self;

    /// Bitwise and with `n` ones
    fn mask(&self, n: usize) -> Self;

    /// Trailing zeros
    fn trailing_zeros(&self) -> usize;

    /// Create all-zeros value
    fn zero() -> Self;

    /// Create value represeting one
    fn one() -> Self;
}

/// A general error code, other errors should implement conversions to/from this
/// if appropriate.
#[derive(Debug)]
pub enum Error {
    /// secp-related error
    Secp256k1(Secp256k1Error),
    /// Serialization error
    Serialize(serialize::Error),
    /// Network error
    Network(network::Error),
    /// The header hash is not below the target
    SpvBadProofOfWork,
    /// The `target` field of a block header did not match the expected difficulty
    SpvBadTarget,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Secp256k1(ref e) => fmt::Display::fmt(e, f),
            Error::Serialize(ref e) => fmt::Display::fmt(e, f),
            Error::Network(ref e) => fmt::Display::fmt(e, f),
            Error::SpvBadProofOfWork => f.write_str("target correct but not attained"),
            Error::SpvBadTarget => f.write_str("target incorrect"),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Error::Secp256k1(ref e) => Some(e),
            Error::Serialize(ref e) => Some(e),
            Error::Network(ref e) => Some(e),
            Error::SpvBadProofOfWork | Error::SpvBadTarget => None,
        }
    }
}

#[doc(hidden)]
impl From<Secp256k1Error> for Error {
    fn from(e: Secp256k1Error) -> Error {
        Error::Secp256k1(e)
    }
}

#[doc(hidden)]
impl From<serialize::Error> for Error {
    fn from(e: serialize::Error) -> Error {
        Error::Serialize(e)
    }
}

#[doc(hidden)]
impl From<network::Error> for Error {
    fn from(e: network::Error) -> Error {
        Error::Network(e)
    }
}
