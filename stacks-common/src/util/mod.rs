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

#[macro_use]
pub mod log;
#[macro_use]
pub mod macros;
pub mod chunked_encoding;
#[cfg(feature = "canonical")]
pub mod db;
pub mod hash;
pub mod pair;
pub mod pipe;
pub mod retry;
pub mod secp256k1;
pub mod uint;
#[cfg(feature = "vrf")]
pub mod vrf;

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{error, fmt, thread, time};

/// Given a relative path inside the Cargo workspace, return the absolute path
pub fn cargo_workspace<P>(relative_path: P) -> PathBuf
where
    P: AsRef<Path>,
{
    let output = std::process::Command::new(env!("CARGO"))
        .arg("locate-project")
        .arg("--workspace")
        .arg("--message-format=plain")
        .output()
        .expect("Failed to run command");
    let cargo_toml = std::str::from_utf8(&output.stdout)
        .expect("Failed to parse utf8")
        .trim();
    Path::new(cargo_toml)
        .parent()
        .expect("Failed to get parent directory")
        .join(relative_path)
}

#[cfg(any(test, feature = "testing"))]
pub mod tests;

pub fn get_epoch_time_secs() -> u64 {
    let start = SystemTime::now();
    let since_the_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    since_the_epoch.as_secs()
}

pub fn get_epoch_time_ms() -> u128 {
    let start = SystemTime::now();
    let since_the_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    since_the_epoch.as_millis()
}

pub fn sleep_ms(millis: u64) {
    let t = time::Duration::from_millis(millis);
    thread::sleep(t);
}

/// Hex deserialization error
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum HexError {
    /// Length was not 64 characters
    BadLength(usize),
    /// Non-hex character in string
    BadCharacter(char),
}

impl fmt::Display for HexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            HexError::BadLength(n) => write!(f, "bad length {} for hex string", n),
            HexError::BadCharacter(c) => write!(f, "bad character {} for hex string", c),
        }
    }
}

impl error::Error for HexError {
    fn cause(&self) -> Option<&dyn error::Error> {
        None
    }
    fn description(&self) -> &str {
        match *self {
            HexError::BadLength(_) => "hex string non-64 length",
            HexError::BadCharacter(_) => "bad hex character",
        }
    }
}

/// Write any `serde_json` object directly to a file
pub fn serialize_json_to_file<J, P>(json: &J, path: P) -> Result<(), std::io::Error>
where
    J: ?Sized + serde::Serialize,
    P: AsRef<Path>,
{
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, json)?;
    writer.flush()
}

/// Read any `serde_json` object directly from a file
pub fn deserialize_json_from_file<J, P>(path: P) -> Result<J, std::io::Error>
where
    J: serde::de::DeserializeOwned,
    P: AsRef<Path>,
{
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    serde_json::from_reader::<_, J>(reader).map_err(std::io::Error::from)
}
