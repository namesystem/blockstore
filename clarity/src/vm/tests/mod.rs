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
use stacks_common::consts::{CHAIN_ID_MAINNET, CHAIN_ID_TESTNET};
use stacks_common::types::StacksEpochId;

pub use super::test_util::*;
use super::ClarityVersion;
use crate::vm::contexts::OwnedEnvironment;
pub use crate::vm::database::BurnStateDB;
use crate::vm::database::MemoryBackingStore;
use crate::vm::errors::Error;
use crate::vm::types::Value;

mod assets;
mod contracts;
mod datamaps;
mod defines;
mod principals;
mod sequences;
#[cfg(test)]
mod simple_apply_eval;
mod traits;
mod variables;

#[cfg(any(test, feature = "testing"))]
impl<'a> OwnedEnvironment<'a> {
    pub fn set_tenure_height(&mut self, tenure_height: u32) {
        self.context.database.begin();
        self.context
            .database
            .set_tenure_height(tenure_height)
            .unwrap();
        self.context.database.commit().unwrap();
    }
}

macro_rules! epochs_template {
    ($($epoch:ident,)*) => {
        #[template]
        #[export]
        #[rstest]
        $(
            #[case::$epoch(StacksEpochId::$epoch)]
        )*
        pub fn test_epochs(#[case] epoch: StacksEpochId) {}

        #[test]
        fn epochs_covered() {
            let epoch = StacksEpochId::latest();
            match epoch {
                // don't test Epoch-1.0
                StacksEpochId::Epoch10 => (),
                // this will lead to a compile time failure if an epoch is left out
                //  of the epochs_template! macro list
                $(StacksEpochId::$epoch)|* => (),
            }
        }
    }
}

macro_rules! clarity_template {
    ($(($epoch:ident, $clarity:ident),)*) => {
        #[template]
        #[export]
        #[rstest]
        $(
            #[case::$epoch(ClarityVersion::$clarity, StacksEpochId::$epoch)]
        )*
        pub fn test_clarity_versions(#[case] version: ClarityVersion, #[case] epoch: StacksEpochId) {}

        #[test]
        fn epoch_clarity_pairs_covered() {
            let epoch = StacksEpochId::latest();
            let clarity = ClarityVersion::latest();
            match (epoch, clarity) {
                // don't test Epoch-1.0
                (StacksEpochId::Epoch10, _) => (),
                // don't test these pairs, because they aren't supported:
                (StacksEpochId::Epoch20, ClarityVersion::Clarity2) => (),
                (StacksEpochId::Epoch2_05, ClarityVersion::Clarity2) => (),
                (StacksEpochId::Epoch20, ClarityVersion::Clarity3) => (),
                (StacksEpochId::Epoch2_05, ClarityVersion::Clarity3) => (),
                (StacksEpochId::Epoch21, ClarityVersion::Clarity3) => (),
                (StacksEpochId::Epoch22, ClarityVersion::Clarity3) => (),
                (StacksEpochId::Epoch23, ClarityVersion::Clarity3) => (),
                (StacksEpochId::Epoch24, ClarityVersion::Clarity3) => (),
                (StacksEpochId::Epoch25, ClarityVersion::Clarity3) => (),
                // this will lead to a compile time failure if a pair is left out
                //  of the clarity_template! macro list
                $((StacksEpochId::$epoch, ClarityVersion::$clarity))|* => (),
            }
        }
    }
}

// Define two rstest templates for Clarity tests: `test_epochs` and `test_clarity_versions`
//  these templates test all epochs (except 1.0) and all valid epoch/clarity-version pairs.
//
// The macro definitions ensure that we get compile time errors in testing if there is a
//  non-covered case in the rstest template. This *could* have been written as a derive macro,
//  but then it would need to be defined in the `stacks-common` library (where it would have to
//  get a `testing` feature flag). This seems less obtuse.
epochs_template! {
    Epoch20,
    Epoch2_05,
    Epoch21,
    Epoch22,
    Epoch23,
    Epoch24,
    Epoch25,
    Epoch30,
    Epoch31,
}

clarity_template! {
    (Epoch20, Clarity1),
    (Epoch2_05, Clarity1),
    (Epoch21, Clarity1),
    (Epoch21, Clarity2),
    (Epoch22, Clarity1),
    (Epoch22, Clarity2),
    (Epoch23, Clarity1),
    (Epoch23, Clarity2),
    (Epoch24, Clarity1),
    (Epoch24, Clarity2),
    (Epoch25, Clarity1),
    (Epoch25, Clarity2),
    (Epoch30, Clarity1),
    (Epoch30, Clarity2),
    (Epoch30, Clarity3),
    (Epoch31, Clarity1),
    (Epoch31, Clarity2),
    (Epoch31, Clarity3),
}

#[cfg(test)]
impl Value {
    pub fn list_from(list_data: Vec<Value>) -> Result<Value, Error> {
        Value::cons_list_unsanitized(list_data)
    }
}

#[fixture]
pub fn env_factory() -> MemoryEnvironmentGenerator {
    MemoryEnvironmentGenerator(MemoryBackingStore::new())
}

#[fixture]
pub fn tl_env_factory() -> TopLevelMemoryEnvironmentGenerator {
    TopLevelMemoryEnvironmentGenerator(MemoryBackingStore::new())
}

pub struct MemoryEnvironmentGenerator(MemoryBackingStore);
impl MemoryEnvironmentGenerator {
    fn get_env(&mut self, epoch: StacksEpochId) -> OwnedEnvironment {
        let mut db = self.0.as_clarity_db();
        db.begin();
        db.set_clarity_epoch_version(epoch).unwrap();
        db.commit().unwrap();
        if epoch.clarity_uses_tip_burn_block() {
            db.begin();
            db.set_tenure_height(1).unwrap();
            db.commit().unwrap();
        }
        let mut owned_env = OwnedEnvironment::new(db, epoch);
        // start an initial transaction.
        owned_env.begin();
        owned_env
    }
}

pub struct TopLevelMemoryEnvironmentGenerator(MemoryBackingStore);
impl TopLevelMemoryEnvironmentGenerator {
    pub fn get_env(&mut self, epoch: StacksEpochId) -> OwnedEnvironment {
        let mut db = self.0.as_clarity_db();
        db.begin();
        db.set_clarity_epoch_version(epoch).unwrap();
        db.commit().unwrap();
        if epoch.clarity_uses_tip_burn_block() {
            db.begin();
            db.set_tenure_height(1).unwrap();
            db.commit().unwrap();
        }
        OwnedEnvironment::new(db, epoch)
    }
}

/// Determine whether or not to use the testnet or mainnet chain ID, given whether or not the
/// caller expects to use mainnet or testnet.
///
/// WARNING TO THE READER:  This is *test-only* code.  The existence of this method does *not*
/// imply that there is a canonical, supported way to convert a `bool` into a chain ID.  The fact
/// that Stacks has a separate chain ID for its testnet (0x80000000) is an accident.  In general, a
/// Stacks blockchain instance only needs _one_ chain ID, and can use the mainnet/testnet field in
/// its transactions to determine whether or not a transaction should be mined in a given chain.
/// Going forward, you should *never* use a different chain ID for your testnet.
///
/// So, do *not* refactor this code to use this conversion in production.
pub fn test_only_mainnet_to_chain_id(mainnet: bool) -> u32 {
    // seriously -- don't even think about it.
    if mainnet {
        CHAIN_ID_MAINNET
    } else {
        CHAIN_ID_TESTNET
    }
}
