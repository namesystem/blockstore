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

use stacks_common::consts::{
    BITCOIN_REGTEST_FIRST_BLOCK_HASH, BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT,
    BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP, FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH,
    MINER_REWARD_MATURITY,
};
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, ConsensusHash, SortitionId, StacksAddress, StacksBlockId,
    TrieHash, VRFSeed,
};
use stacks_common::types::{StacksEpoch as GenericStacksEpoch, StacksEpochId};
use stacks_common::util::hash::{to_hex, Hash160, Sha512Trunc256Sum};

use super::clarity_store::SpecialCaseHandler;
use super::key_value_wrapper::ValueResult;
use crate::vm::analysis::{AnalysisDatabase, ContractAnalysis};
use crate::vm::ast::ASTRules;
use crate::vm::contracts::Contract;
use crate::vm::costs::{CostOverflowingMath, ExecutionCost};
use crate::vm::database::structures::{
    ClarityDeserializable, ClaritySerializable, DataMapMetadata, DataVariableMetadata,
    FungibleTokenMetadata, NonFungibleTokenMetadata, STXBalance, STXBalanceSnapshot,
};
use crate::vm::database::{ClarityBackingStore, RollbackWrapper};
use crate::vm::errors::{
    CheckErrors, Error, InterpreterError, InterpreterResult as Result, RuntimeErrorType,
};
use crate::vm::representations::ClarityName;
use crate::vm::types::serialization::NONE_SERIALIZATION_LEN;
use crate::vm::types::{
    byte_len_of_serialization, PrincipalData, QualifiedContractIdentifier, StandardPrincipalData,
    TupleData, TypeSignature, Value,
};

pub const STORE_CONTRACT_SRC_INTERFACE: bool = true;
const TENURE_HEIGHT_KEY: &str = "_stx-data::tenure_height";

pub type StacksEpoch = GenericStacksEpoch<ExecutionCost>;

#[repr(u8)]
pub enum StoreType {
    DataMap = 0x00,
    Variable = 0x01,
    FungibleToken = 0x02,
    CirculatingSupply = 0x03,
    NonFungibleToken = 0x04,
    DataMapMeta = 0x05,
    VariableMeta = 0x06,
    FungibleTokenMeta = 0x07,
    NonFungibleTokenMeta = 0x08,
    Contract = 0x09,
    SimmedBlock = 0x10,
    SimmedBlockHeight = 0x11,
    Nonce = 0x12,
    STXBalance = 0x13,
    PoxSTXLockup = 0x14,
    PoxUnlockHeight = 0x15,
}

impl TryFrom<&str> for StoreType {
    type Error = String;

    fn try_from(value: &str) -> core::result::Result<Self, Self::Error> {
        use self::StoreType::*;

        let hex_value = value.parse::<u8>().map_err(|e| e.to_string())?;
        match hex_value {
            0x00 => Ok(DataMap),
            0x01 => Ok(Variable),
            0x02 => Ok(FungibleToken),
            0x03 => Ok(CirculatingSupply),
            0x04 => Ok(NonFungibleToken),
            0x05 => Ok(DataMapMeta),
            0x06 => Ok(VariableMeta),
            0x07 => Ok(FungibleTokenMeta),
            0x08 => Ok(NonFungibleTokenMeta),
            0x09 => Ok(Contract),
            0x10 => Ok(SimmedBlock),
            0x11 => Ok(SimmedBlockHeight),
            0x12 => Ok(Nonce),
            0x13 => Ok(STXBalance),
            0x14 => Ok(PoxSTXLockup),
            0x15 => Ok(PoxUnlockHeight),
            _ => Err("Invalid StoreType".into()),
        }
    }
}

pub enum ContractDataVarName {
    Contract,
    ContractSize,
    ContractSrc,
    ContractDataSize,
}

impl ContractDataVarName {
    pub fn as_str(&self) -> &str {
        match self {
            Self::Contract => "contract",
            Self::ContractSize => "contract-size",
            Self::ContractSrc => "contract-src",
            Self::ContractDataSize => "contract-data-size",
        }
    }
}

impl TryFrom<&str> for ContractDataVarName {
    type Error = String;

    fn try_from(value: &str) -> core::result::Result<Self, Self::Error> {
        use self::ContractDataVarName::*;
        match value {
            "contract" => Ok(Contract),
            "contract-size" => Ok(ContractSize),
            "contract-src" => Ok(ContractSrc),
            "contract-data-size" => Ok(ContractDataSize),
            _ => Err("Invalid ContractDataVarName".into()),
        }
    }
}

pub struct ClarityDatabase<'a> {
    pub store: RollbackWrapper<'a>,
    headers_db: &'a dyn HeadersDB,
    burn_state_db: &'a dyn BurnStateDB,
}

pub trait HeadersDB {
    fn get_stacks_block_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<BlockHeaderHash>;
    fn get_burn_header_hash_for_block(&self, id_bhh: &StacksBlockId)
        -> Option<BurnchainHeaderHash>;
    fn get_consensus_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<ConsensusHash>;
    fn get_vrf_seed_for_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<VRFSeed>;
    fn get_stacks_block_time_for_block(&self, id_bhh: &StacksBlockId) -> Option<u64>;
    fn get_burn_block_time_for_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: Option<&StacksEpochId>,
    ) -> Option<u64>;
    fn get_burn_block_height_for_block(&self, id_bhh: &StacksBlockId) -> Option<u32>;
    fn get_miner_address(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<StacksAddress>;
    fn get_burnchain_tokens_spent_for_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<u128>;
    fn get_burnchain_tokens_spent_for_winning_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<u128>;
    fn get_tokens_earned_for_block(
        &self,
        id_bhh: &StacksBlockId,
        epoch: &StacksEpochId,
    ) -> Option<u128>;
    fn get_stacks_height_for_tenure_height(
        &self,
        tip: &StacksBlockId,
        tenure_height: u32,
    ) -> Option<u32>;
}

pub trait BurnStateDB {
    /// Get the burn chain height at the current tip.
    fn get_tip_burn_block_height(&self) -> Option<u32>;
    /// Get the sortition id for the current tip.
    fn get_tip_sortition_id(&self) -> Option<SortitionId>;

    fn get_v1_unlock_height(&self) -> u32;
    fn get_v2_unlock_height(&self) -> u32;
    fn get_v3_unlock_height(&self) -> u32;
    fn get_pox_3_activation_height(&self) -> u32;
    fn get_pox_4_activation_height(&self) -> u32;

    /// Returns the *burnchain block height* for the `sortition_id` is associated with.
    fn get_burn_block_height(&self, sortition_id: &SortitionId) -> Option<u32>;

    /// Returns the height of the burnchain when the Stacks chain started running.
    fn get_burn_start_height(&self) -> u32;

    fn get_pox_prepare_length(&self) -> u32;
    fn get_pox_reward_cycle_length(&self) -> u32;
    fn get_pox_rejection_fraction(&self) -> u64;

    /// Returns the burnchain header hash for the given burn block height, as queried from the given SortitionId.
    ///
    /// Returns Some if `self.get_burn_start_height() <= height < self.get_burn_block_height(sorition_id)`, and None otherwise.
    fn get_burn_header_hash(
        &self,
        height: u32,
        sortition_id: &SortitionId,
    ) -> Option<BurnchainHeaderHash>;

    /// Lookup a `SortitionId` keyed to a `ConsensusHash`.
    ///
    /// Returns None if no block found.
    fn get_sortition_id_from_consensus_hash(
        &self,
        consensus_hash: &ConsensusHash,
    ) -> Option<SortitionId>;

    /// The epoch is defined as by a start and end height. This returns
    /// the epoch enclosing `height`.
    fn get_stacks_epoch(&self, height: u32) -> Option<StacksEpoch>;
    fn get_stacks_epoch_by_epoch_id(&self, epoch_id: &StacksEpochId) -> Option<StacksEpoch>;

    fn get_ast_rules(&self, height: u32) -> ASTRules;

    /// Get the PoX payout addresses for a given burnchain block
    fn get_pox_payout_addrs(
        &self,
        height: u32,
        sortition_id: &SortitionId,
    ) -> Option<(Vec<TupleData>, u128)>;
}

pub struct NullHeadersDB {}
pub struct NullBurnStateDB {
    epoch: StacksEpochId,
}

pub const NULL_HEADER_DB: NullHeadersDB = NullHeadersDB {};
pub const NULL_BURN_STATE_DB: NullBurnStateDB = NullBurnStateDB {
    epoch: StacksEpochId::Epoch20,
};

impl HeadersDB for NullHeadersDB {
    fn get_burn_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
    ) -> Option<BurnchainHeaderHash> {
        if *id_bhh == StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH)
        {
            #[allow(clippy::unwrap_used)]
            let first_block_hash =
                BurnchainHeaderHash::from_hex(BITCOIN_REGTEST_FIRST_BLOCK_HASH).unwrap();
            Some(first_block_hash)
        } else {
            None
        }
    }
    fn get_vrf_seed_for_block(
        &self,
        _bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<VRFSeed> {
        None
    }
    fn get_stacks_block_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<BlockHeaderHash> {
        if *id_bhh == StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH)
        {
            Some(FIRST_STACKS_BLOCK_HASH)
        } else {
            None
        }
    }
    fn get_consensus_hash_for_block(
        &self,
        _id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<ConsensusHash> {
        None
    }
    fn get_burn_block_time_for_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: Option<&StacksEpochId>,
    ) -> Option<u64> {
        if *id_bhh == StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH)
        {
            Some(BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP as u64)
        } else {
            None
        }
    }
    fn get_stacks_block_time_for_block(&self, _id_bhh: &StacksBlockId) -> Option<u64> {
        None
    }
    fn get_burn_block_height_for_block(&self, id_bhh: &StacksBlockId) -> Option<u32> {
        if *id_bhh == StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH)
        {
            Some(BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT as u32)
        } else {
            Some(1)
        }
    }
    fn get_miner_address(
        &self,
        _id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<StacksAddress> {
        None
    }
    fn get_burnchain_tokens_spent_for_block(
        &self,
        _id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<u128> {
        None
    }
    fn get_burnchain_tokens_spent_for_winning_block(
        &self,
        _id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<u128> {
        None
    }
    fn get_tokens_earned_for_block(
        &self,
        _id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<u128> {
        None
    }
    fn get_stacks_height_for_tenure_height(
        &self,
        _tip: &StacksBlockId,
        _tenure_height: u32,
    ) -> Option<u32> {
        None
    }
}

#[allow(clippy::panic)]
impl BurnStateDB for NullBurnStateDB {
    fn get_tip_burn_block_height(&self) -> Option<u32> {
        Some(0)
    }

    fn get_tip_sortition_id(&self) -> Option<SortitionId> {
        None
    }

    fn get_burn_block_height(&self, _sortition_id: &SortitionId) -> Option<u32> {
        None
    }

    fn get_burn_start_height(&self) -> u32 {
        0
    }

    fn get_sortition_id_from_consensus_hash(
        &self,
        _consensus_hash: &ConsensusHash,
    ) -> Option<SortitionId> {
        None
    }

    fn get_burn_header_hash(
        &self,
        _height: u32,
        _sortition_id: &SortitionId,
    ) -> Option<BurnchainHeaderHash> {
        None
    }

    fn get_stacks_epoch(&self, _height: u32) -> Option<StacksEpoch> {
        Some(StacksEpoch {
            epoch_id: self.epoch,
            start_height: 0,
            end_height: u64::MAX,
            block_limit: ExecutionCost::max_value(),
            network_epoch: 0,
        })
    }
    fn get_stacks_epoch_by_epoch_id(&self, _epoch_id: &StacksEpochId) -> Option<StacksEpoch> {
        self.get_stacks_epoch(0)
    }

    fn get_v1_unlock_height(&self) -> u32 {
        u32::MAX
    }

    fn get_v2_unlock_height(&self) -> u32 {
        u32::MAX
    }

    fn get_v3_unlock_height(&self) -> u32 {
        u32::MAX
    }

    fn get_pox_3_activation_height(&self) -> u32 {
        u32::MAX
    }

    fn get_pox_4_activation_height(&self) -> u32 {
        u32::MAX
    }

    fn get_pox_prepare_length(&self) -> u32 {
        panic!("NullBurnStateDB should not return PoX info");
    }

    fn get_pox_reward_cycle_length(&self) -> u32 {
        panic!("NullBurnStateDB should not return PoX info");
    }

    fn get_pox_rejection_fraction(&self) -> u64 {
        panic!("NullBurnStateDB should not return PoX info");
    }
    fn get_pox_payout_addrs(
        &self,
        _height: u32,
        _sortition_id: &SortitionId,
    ) -> Option<(Vec<TupleData>, u128)> {
        None
    }

    fn get_ast_rules(&self, _height: u32) -> ASTRules {
        ASTRules::Typical
    }
}

impl<'a> ClarityDatabase<'a> {
    pub fn new(
        store: &'a mut dyn ClarityBackingStore,
        headers_db: &'a dyn HeadersDB,
        burn_state_db: &'a dyn BurnStateDB,
    ) -> ClarityDatabase<'a> {
        ClarityDatabase {
            store: RollbackWrapper::new(store),
            headers_db,
            burn_state_db,
        }
    }

    pub fn new_with_rollback_wrapper(
        store: RollbackWrapper<'a>,
        headers_db: &'a dyn HeadersDB,
        burn_state_db: &'a dyn BurnStateDB,
    ) -> ClarityDatabase<'a> {
        ClarityDatabase {
            store,
            headers_db,
            burn_state_db,
        }
    }

    pub fn initialize(&mut self) {}

    pub fn is_stack_empty(&self) -> bool {
        self.store.depth() == 0
    }

    /// Nest the key-value wrapper instance
    pub fn begin(&mut self) {
        self.store.nest();
    }

    /// Commit current key-value wrapper layer
    pub fn commit(&mut self) -> Result<()> {
        self.store.commit().map_err(|e| e.into())
    }

    /// Drop current key-value wrapper layer
    pub fn roll_back(&mut self) -> Result<()> {
        self.store.rollback().map_err(|e| e.into())
    }

    pub fn set_block_hash(
        &mut self,
        bhh: StacksBlockId,
        query_pending_data: bool,
    ) -> Result<StacksBlockId> {
        self.store.set_block_hash(bhh, query_pending_data)
    }

    pub fn put_data<T: ClaritySerializable>(&mut self, key: &str, value: &T) -> Result<()> {
        self.store.put_data(key, &value.serialize())
    }

    /// Like `put()`, but returns the serialized byte size of the stored value
    pub fn put_data_with_size<T: ClaritySerializable>(
        &mut self,
        key: &str,
        value: &T,
    ) -> Result<u64> {
        let serialized = value.serialize();
        self.store.put_data(key, &serialized)?;
        Ok(byte_len_of_serialization(&serialized))
    }

    pub fn get_data<T>(&mut self, key: &str) -> Result<Option<T>>
    where
        T: ClarityDeserializable<T>,
    {
        self.store.get_data::<T>(key)
    }

    pub fn get_data_by_hash<T>(&mut self, hash: &TrieHash) -> Result<Option<T>>
    where
        T: ClarityDeserializable<T>,
    {
        self.store.get_data_by_hash::<T>(hash)
    }

    pub fn put_value(&mut self, key: &str, value: Value, epoch: &StacksEpochId) -> Result<()> {
        self.put_value_with_size(key, value, epoch)?;
        Ok(())
    }

    pub fn put_value_with_size(
        &mut self,
        key: &str,
        value: Value,
        epoch: &StacksEpochId,
    ) -> Result<u64> {
        let sanitize = epoch.value_sanitizing();
        let mut pre_sanitized_size = None;

        let serialized = if sanitize {
            let value_size = value
                .serialized_size()
                .map_err(|e| InterpreterError::Expect(e.to_string()))?
                as u64;

            let (sanitized_value, did_sanitize) =
                Value::sanitize_value(epoch, &TypeSignature::type_of(&value)?, value)
                    .ok_or_else(|| CheckErrors::CouldNotDetermineType)?;
            // if data needed to be sanitized *charge* for the unsanitized cost
            if did_sanitize {
                pre_sanitized_size = Some(value_size);
            }
            sanitized_value.serialize_to_vec()?
        } else {
            value.serialize_to_vec()?
        };

        let size = serialized.len() as u64;
        let hex_serialized = to_hex(serialized.as_slice());
        self.store.put_data(key, &hex_serialized)?;

        Ok(pre_sanitized_size.unwrap_or(size))
    }

    pub fn get_value(
        &mut self,
        key: &str,
        expected: &TypeSignature,
        epoch: &StacksEpochId,
    ) -> Result<Option<ValueResult>> {
        self.store
            .get_value(key, expected, epoch)
            .map_err(|e| InterpreterError::DBError(e.to_string()).into())
    }

    pub fn get_data_with_proof<T>(&mut self, key: &str) -> Result<Option<(T, Vec<u8>)>>
    where
        T: ClarityDeserializable<T>,
    {
        self.store.get_data_with_proof(key)
    }

    pub fn get_data_with_proof_by_hash<T>(
        &mut self,
        hash: &TrieHash,
    ) -> Result<Option<(T, Vec<u8>)>>
    where
        T: ClarityDeserializable<T>,
    {
        self.store.get_data_with_proof_by_hash(hash)
    }

    pub fn make_key_for_trip(
        contract_identifier: &QualifiedContractIdentifier,
        data: StoreType,
        var_name: &str,
    ) -> String {
        format!("vm::{}::{}::{}", contract_identifier, data as u8, var_name)
    }

    pub fn make_metadata_key(data: StoreType, var_name: &str) -> String {
        format!("vm-metadata::{}::{}", data as u8, var_name)
    }

    fn clarity_state_epoch_key() -> &'static str {
        "vm-epoch::epoch-version"
    }

    pub fn make_key_for_quad(
        contract_identifier: &QualifiedContractIdentifier,
        data: StoreType,
        var_name: &str,
        key_value: &str,
    ) -> String {
        format!(
            "vm::{}::{}::{}::{}",
            contract_identifier, data as u8, var_name, key_value
        )
    }

    pub fn insert_contract_hash(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        contract_content: &str,
    ) -> Result<()> {
        let hash = Sha512Trunc256Sum::from_data(contract_content.as_bytes());
        self.store
            .prepare_for_contract_metadata(contract_identifier, hash)?;
        // insert contract-size
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::ContractSize.as_str(),
        );
        self.insert_metadata(contract_identifier, &key, &(contract_content.len() as u64))?;

        // insert contract-src
        if STORE_CONTRACT_SRC_INTERFACE {
            let key = ClarityDatabase::make_metadata_key(
                StoreType::Contract,
                ContractDataVarName::ContractSrc.as_str(),
            );
            self.insert_metadata(contract_identifier, &key, &contract_content.to_string())?;
        }
        Ok(())
    }

    pub fn get_contract_src(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Option<String> {
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::ContractSrc.as_str(),
        );
        self.fetch_metadata(contract_identifier, &key)
            .ok()
            .flatten()
    }

    pub fn set_metadata(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        key: &str,
        data: &str,
    ) -> Result<()> {
        self.store
            .insert_metadata(contract_identifier, key, data)
            .map_err(|e| e.into())
    }

    /// Set a metadata entry if it hasn't already been set, yielding
    ///  a runtime error if it was. This should only be called by post-nakamoto
    ///  contexts.
    pub fn try_set_metadata(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        key: &str,
        data: &str,
    ) -> Result<()> {
        if self.store.has_metadata_entry(contract_identifier, key) {
            Err(Error::Runtime(RuntimeErrorType::MetadataAlreadySet, None))
        } else {
            Ok(self.store.insert_metadata(contract_identifier, key, data)?)
        }
    }

    fn insert_metadata<T: ClaritySerializable>(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        key: &str,
        data: &T,
    ) -> Result<()> {
        if self.store.has_metadata_entry(contract_identifier, key) {
            Err(InterpreterError::Expect(format!(
                "Metadata entry '{}' already exists for contract: {}",
                key, contract_identifier
            ))
            .into())
        } else {
            self.store
                .insert_metadata(contract_identifier, key, &data.serialize())
                .map_err(|e| e.into())
        }
    }

    fn fetch_metadata<T>(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        key: &str,
    ) -> Result<Option<T>>
    where
        T: ClarityDeserializable<T>,
    {
        let x_opt = self.store.get_metadata(contract_identifier, key)?;
        match x_opt {
            None => Ok(None),
            Some(x) => T::deserialize(&x).map(|out| Some(out)),
        }
    }

    pub fn fetch_metadata_manual<T>(
        &mut self,
        at_height: u32,
        contract_identifier: &QualifiedContractIdentifier,
        key: &str,
    ) -> Result<Option<T>>
    where
        T: ClarityDeserializable<T>,
    {
        let x_opt = self
            .store
            .get_metadata_manual(at_height, contract_identifier, key)?;
        match x_opt {
            None => Ok(None),
            Some(x) => T::deserialize(&x).map(|out| Some(out)),
        }
    }

    // load contract analysis stored by an analysis_db instance.
    //   in unit testing, where the interpreter is invoked without
    //   an analysis pass, this function will fail to find contract
    //   analysis data
    pub fn load_contract_analysis(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Option<ContractAnalysis>> {
        self.store
            .get_metadata(contract_identifier, AnalysisDatabase::storage_key())
            // treat NoSuchContract error thrown by get_metadata as an Option::None --
            //    the analysis will propagate that as a CheckError anyways.
            .ok()
            .flatten()
            .map(|x| ContractAnalysis::deserialize(&x))
            .transpose()
    }

    pub fn get_contract_size(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<u64> {
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::ContractSize.as_str(),
        );
        let contract_size: u64 =
            self.fetch_metadata(contract_identifier, &key)?
                .ok_or_else(|| {
                    InterpreterError::Expect(
            "Failed to read non-consensus contract metadata, even though contract exists in MARF."
        .into())
                })?;
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::ContractDataSize.as_str(),
        );
        let data_size: u64 = self
            .fetch_metadata(contract_identifier, &key)?
            .ok_or_else(|| {
                InterpreterError::Expect(
            "Failed to read non-consensus contract metadata, even though contract exists in MARF."
        .into())
            })?;

        // u64 overflow is _checked_ on insert into contract-data-size
        Ok(data_size + contract_size)
    }

    /// used for adding the memory usage of `define-constant` variables.
    pub fn set_contract_data_size(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        data_size: u64,
    ) -> Result<()> {
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::ContractSize.as_str(),
        );
        let contract_size: u64 =
            self.fetch_metadata(contract_identifier, &key)?
                .ok_or_else(|| {
                    InterpreterError::Expect(
            "Failed to read non-consensus contract metadata, even though contract exists in MARF."
        .into())
                })?;
        contract_size.cost_overflow_add(data_size)?;

        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::ContractDataSize.as_str(),
        );
        self.insert_metadata(contract_identifier, &key, &data_size)?;
        Ok(())
    }

    pub fn insert_contract(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        contract: Contract,
    ) -> Result<()> {
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::Contract.as_str(),
        );
        self.insert_metadata(contract_identifier, &key, &contract)?;
        Ok(())
    }

    pub fn has_contract(&mut self, contract_identifier: &QualifiedContractIdentifier) -> bool {
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::Contract.as_str(),
        );
        self.store.has_metadata_entry(contract_identifier, &key)
    }

    pub fn get_contract(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
    ) -> Result<Contract> {
        let key = ClarityDatabase::make_metadata_key(
            StoreType::Contract,
            ContractDataVarName::Contract.as_str(),
        );
        let mut data: Contract = self.fetch_metadata(contract_identifier, &key)?
            .ok_or_else(|| InterpreterError::Expect(
                "Failed to read non-consensus contract metadata, even though contract exists in MARF."
                .into()))?;
        data.canonicalize_types(&self.get_clarity_epoch_version()?);
        Ok(data)
    }

    pub fn ustx_liquid_supply_key() -> &'static str {
        "_stx-data::ustx_liquid_supply"
    }

    /// Returns the epoch version currently applied in the stored Clarity state.
    /// Since Clarity did not exist in stacks 1.0, the lowest valid epoch ID is stacks 2.0.
    /// The instantiation of subsequent epochs may bump up the epoch version in the clarity DB if
    /// Clarity is updated in that epoch.
    pub fn get_clarity_epoch_version(&mut self) -> Result<StacksEpochId> {
        let out = match self.get_data(Self::clarity_state_epoch_key())? {
            Some(x) => u32::try_into(x).map_err(|_| {
                InterpreterError::Expect("Bad Clarity epoch version in stored Clarity state".into())
            })?,
            None => StacksEpochId::Epoch20,
        };
        Ok(out)
    }

    /// Should be called _after_ all of the epoch's initialization has been invoked
    pub fn set_clarity_epoch_version(&mut self, epoch: StacksEpochId) -> Result<()> {
        self.put_data(Self::clarity_state_epoch_key(), &(epoch as u32))
    }

    /// Returns the _current_ total liquid ustx
    pub fn get_total_liquid_ustx(&mut self) -> Result<u128> {
        Ok(self
            .get_value(
                ClarityDatabase::ustx_liquid_supply_key(),
                &TypeSignature::UIntType,
                &StacksEpochId::latest(),
            )
            .map_err(|_| {
                InterpreterError::Expect(
                    "FATAL: failed to load ustx_liquid_supply Clarity key".into(),
                )
            })?
            .map(|v| v.value.expect_u128())
            .transpose()?
            .unwrap_or(0))
    }

    fn set_ustx_liquid_supply(&mut self, set_to: u128) -> Result<()> {
        self.put_value(
            ClarityDatabase::ustx_liquid_supply_key(),
            Value::UInt(set_to),
            // okay to pin epoch, because ustx_liquid_supply does not need to sanitize
            &StacksEpochId::Epoch21,
        )
        .map_err(|_| {
            InterpreterError::Expect("FATAL: Failed to store STX liquid supply".into()).into()
        })
    }

    pub fn increment_ustx_liquid_supply(&mut self, incr_by: u128) -> Result<()> {
        let current = self.get_total_liquid_ustx()?;
        let next = current.checked_add(incr_by).ok_or_else(|| {
            error!("Overflowed `ustx-liquid-supply`");
            RuntimeErrorType::ArithmeticOverflow
        })?;
        self.set_ustx_liquid_supply(next)?;
        Ok(())
    }

    pub fn decrement_ustx_liquid_supply(&mut self, decr_by: u128) -> Result<()> {
        let current = self.get_total_liquid_ustx()?;
        let next = current.checked_sub(decr_by).ok_or_else(|| {
            error!("`stx-burn?` accepted that reduces `ustx-liquid-supply` below 0");
            RuntimeErrorType::ArithmeticUnderflow
        })?;
        self.set_ustx_liquid_supply(next)?;
        Ok(())
    }

    /// Returns the tenure height of the current block.
    pub fn get_tenure_height(&mut self) -> Result<u32> {
        if self.get_clarity_epoch_version()? < StacksEpochId::Epoch30 {
            // Before epoch 3.0, the tenure height was not stored in the
            // Clarity state. Instead, it was the same as the block height.
            return Ok(self.get_current_block_height());
        }

        self.get_data(TENURE_HEIGHT_KEY)?
            .ok_or_else(|| {
                InterpreterError::Expect("No tenure height in stored Clarity state".into()).into()
            })
            .and_then(|x| {
                u32::try_into(x).map_err(|_| {
                    InterpreterError::Expect("Bad tenure height in stored Clarity state".into())
                        .into()
                })
            })
    }

    /// Set the tenure height of the current block. In the first block of a new
    /// tenure, this height must be incremented before evaluating any
    /// transactions in the block.
    pub fn set_tenure_height(&mut self, height: u32) -> Result<()> {
        if self.get_clarity_epoch_version()? < StacksEpochId::Epoch30 {
            return Err(Error::Interpreter(InterpreterError::Expect(
                "Setting tenure height in Clarity state is not supported before epoch 3.0".into(),
            )));
        }
        self.put_data(TENURE_HEIGHT_KEY, &height)
    }

    pub fn destroy(self) -> RollbackWrapper<'a> {
        self.store
    }

    pub fn is_in_regtest(&self) -> bool {
        cfg!(test)
    }
}

// Get block information

impl ClarityDatabase<'_> {
    /// Returns the ID of a *Stacks* block, by a *Stacks* block height.
    ///
    /// Fails if `block_height` >= the "currently" under construction Stacks block height.
    pub fn get_index_block_header_hash(&mut self, block_height: u32) -> Result<StacksBlockId> {
        self.store
            .get_block_header_hash(block_height)
            // the caller is responsible for ensuring that the block_height given
            //  is < current_block_height, so this should _always_ return a value.
            .ok_or_else(|| {
                InterpreterError::Expect(
                    "Block header hash must return for provided block height".into(),
                )
                .into()
            })
    }

    /// This is the height we are currently constructing. It comes from the MARF.
    pub fn get_current_block_height(&mut self) -> u32 {
        self.store.get_current_block_height()
    }

    /// Return the height for PoX v1 -> v2 auto unlocks
    ///   from the burn state db
    pub fn get_v1_unlock_height(&self) -> u32 {
        self.burn_state_db.get_v1_unlock_height()
    }

    /// Return the height for PoX 3 activation from the burn state db
    pub fn get_pox_3_activation_height(&self) -> u32 {
        self.burn_state_db.get_pox_3_activation_height()
    }

    /// Return the height for PoX 4 activation from the burn state db
    pub fn get_pox_4_activation_height(&self) -> u32 {
        self.burn_state_db.get_pox_4_activation_height()
    }

    /// Return the height for PoX v2 -> v3 auto unlocks
    ///   from the burn state db
    pub fn get_v2_unlock_height(&mut self) -> Result<u32> {
        if self.get_clarity_epoch_version()? >= StacksEpochId::Epoch22 {
            Ok(self.burn_state_db.get_v2_unlock_height())
        } else {
            Ok(u32::MAX)
        }
    }

    /// Return the height for PoX v3 -> v4 auto unlocks
    ///   from the burn state db
    pub fn get_v3_unlock_height(&mut self) -> Result<u32> {
        if self.get_clarity_epoch_version()? >= StacksEpochId::Epoch25 {
            Ok(self.burn_state_db.get_v3_unlock_height())
        } else {
            Ok(u32::MAX)
        }
    }

    /// Return the block height for a given tenure height
    ///   if the block information is queryable for the tenure height.
    /// The block information for a given tenure height is queryable iff:
    ///  * `tenure_height` falls in 2.x, and `tenure_height` < `current_height`
    ///  * `tenure_height` falls in 3.x, and the first block of the tenure
    ///    at `tenure_height` has a stacks block height less than `current_height`
    ///
    /// If the block information isn't queryable, return `Ok(None)`
    pub fn get_block_height_for_tenure_height(
        &mut self,
        tenure_height: u32,
    ) -> Result<Option<u32>> {
        let current_tenure_height = self.get_tenure_height()?;
        if current_tenure_height < tenure_height {
            return Ok(None);
        }
        let current_height = self.get_current_block_height();
        if current_height <= tenure_height {
            return Ok(None);
        }
        // check if we're querying a 2.x block
        let id_bhh = self.get_index_block_header_hash(tenure_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        if !epoch.uses_nakamoto_blocks() {
            return Ok(Some(tenure_height));
        }
        // query from the parent
        let query_tip = self.get_index_block_header_hash(current_height.saturating_sub(1))?;
        Ok(self
            .headers_db
            .get_stacks_height_for_tenure_height(&query_tip, tenure_height))
    }

    /// Get the last-known burnchain block height.
    /// Note that this is _not_ the burnchain height in which this block was mined!
    /// This is the burnchain block height of the parent of the Stacks block at the current Stacks
    /// block height (i.e. that returned by `get_index_block_header_hash` for
    /// `get_current_block_height`).
    pub fn get_current_burnchain_block_height(&mut self) -> Result<u32> {
        let epoch = self.get_clarity_epoch_version()?;
        match epoch {
            // Special case to preserve possibly incorrect behavior (inside at-block) in Epoch 3.0
            StacksEpochId::Epoch30 => {
                self.burn_state_db
                    .get_tip_burn_block_height()
                    .ok_or_else(|| {
                        InterpreterError::Expect("Failed to get burnchain tip height.".into())
                            .into()
                    })
            }
            _ => {
                let cur_stacks_height = self.store.get_current_block_height();

                // Before epoch 3.0, we can only access the burn block associated with the last block
                let last_mined_bhh = if epoch.clarity_uses_tip_burn_block() {
                    // In epoch 3+, we can access the current burnchain block
                    self.get_index_block_header_hash(cur_stacks_height)
                        .or_else(|_| self.get_index_block_header_hash(cur_stacks_height - 1))?
                } else if cur_stacks_height == 0 {
                    return Ok(self.burn_state_db.get_burn_start_height());
                } else {
                    // Safety note: normal subtraction is safe here, because we've already checked
                    // that cur_stacks_height > 0.
                    self.get_index_block_header_hash(cur_stacks_height - 1)?
                };

                self.get_burnchain_block_height(&last_mined_bhh)
                    .ok_or_else(|| {
                        InterpreterError::Expect(format!(
                            "Block header hash '{last_mined_bhh}' must return for provided stacks block height {cur_stacks_height}"
                        ))
                        .into()
                    })
            }
        }
    }

    pub fn get_block_header_hash(&mut self, block_height: u32) -> Result<BlockHeaderHash> {
        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        self.headers_db
            .get_stacks_block_header_hash_for_block(&id_bhh, &epoch)
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()).into())
    }

    pub fn get_burn_block_time(
        &mut self,
        block_height: u32,
        id_bhh_opt: Option<StacksBlockId>,
    ) -> Result<u64> {
        let id_bhh = match id_bhh_opt {
            Some(x) => x,
            None => self.get_index_block_header_hash(block_height)?,
        };
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        self.headers_db
            .get_burn_block_time_for_block(&id_bhh, Some(&epoch))
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()).into())
    }

    pub fn get_block_time(&mut self, block_height: u32) -> Result<u64> {
        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        if !epoch.uses_nakamoto_blocks() {
            return self.get_burn_block_time(block_height, Some(id_bhh));
        }

        self.headers_db
            .get_stacks_block_time_for_block(&id_bhh)
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()).into())
    }

    pub fn get_burnchain_block_header_hash(
        &mut self,
        block_height: u32,
    ) -> Result<BurnchainHeaderHash> {
        let id_bhh = self.get_index_block_header_hash(block_height)?;
        self.headers_db
            .get_burn_header_hash_for_block(&id_bhh)
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()).into())
    }

    /// In Epoch 2.x:
    /// 1. Get the current Stacks tip height (which is in the process of being evaluated)
    /// 2. Get the parent block's StacksBlockId, which is SHA512-256(consensus_hash, block_hash).
    ///    This is the highest Stacks block in this fork whose consensus hash is known.
    /// 3. Resolve the parent StacksBlockId to its consensus hash
    /// 4. Resolve the consensus hash to the associated SortitionId
    ///    In Epoch 3+:
    /// 1. Get the SortitionId of the current Stacks tip
    fn get_sortition_id_for_stacks_tip(&mut self) -> Result<Option<SortitionId>> {
        if !self
            .get_clarity_epoch_version()?
            .clarity_uses_tip_burn_block()
        {
            let current_stacks_height = self.get_current_block_height();

            if current_stacks_height < 1 {
                // we are in the Stacks genesis block
                return Ok(None);
            }

            // this is the StacksBlockId of the last block evaluated in this fork
            let parent_id_bhh = self.get_index_block_header_hash(current_stacks_height - 1)?;
            let epoch = self.get_stacks_epoch_for_block(&parent_id_bhh)?;

            // infallible, since we always store the consensus hash with the StacksBlockId in the
            // headers DB
            let consensus_hash = self
                .headers_db
                .get_consensus_hash_for_block(&parent_id_bhh, &epoch)
                .ok_or_else(|| {
                    InterpreterError::Expect(format!(
                        "FATAL: no consensus hash found for StacksBlockId {}",
                        &parent_id_bhh
                    ))
                })?;

            // infallible, since every sortition has a consensus hash
            let sortition_id = self
                .burn_state_db
                .get_sortition_id_from_consensus_hash(&consensus_hash)
                .ok_or_else(|| {
                    InterpreterError::Expect(format!(
                        "FATAL: no SortitionID found for consensus hash {}",
                        &consensus_hash
                    ))
                })?;

            Ok(Some(sortition_id))
        } else {
            Ok(self.burn_state_db.get_tip_sortition_id())
        }
    }

    /// Fetch the burnchain block header hash for a given burnchain height.
    /// Because the burnchain can fork, we need to resolve the burnchain hash from the
    /// currently-evaluated Stacks chain tip.
    ///
    /// This way, the `BurnchainHeaderHash` returned is guaranteed to be on the burnchain fork
    /// that holds the currently-evaluated Stacks fork (even if it's not the canonical burnchain
    /// fork).
    pub fn get_burnchain_block_header_hash_for_burnchain_height(
        &mut self,
        burnchain_block_height: u32,
    ) -> Result<Option<BurnchainHeaderHash>> {
        let sortition_id = match self.get_sortition_id_for_stacks_tip()? {
            Some(x) => x,
            None => return Ok(None),
        };
        Ok(self
            .burn_state_db
            .get_burn_header_hash(burnchain_block_height, &sortition_id))
    }

    /// Get the PoX reward addresses and per-address payout for a given burnchain height.  Because the burnchain can fork,
    /// we need to resolve the PoX addresses from the currently-evaluated Stacks chain tip.
    pub fn get_pox_payout_addrs_for_burnchain_height(
        &mut self,
        burnchain_block_height: u32,
    ) -> Result<Option<(Vec<TupleData>, u128)>> {
        let sortition_id = match self.get_sortition_id_for_stacks_tip()? {
            Some(x) => x,
            None => return Ok(None),
        };
        Ok(self
            .burn_state_db
            .get_pox_payout_addrs(burnchain_block_height, &sortition_id))
    }

    pub fn get_burnchain_block_height(&self, id_bhh: &StacksBlockId) -> Option<u32> {
        self.headers_db.get_burn_block_height_for_block(id_bhh)
    }

    pub fn get_block_vrf_seed(&mut self, block_height: u32) -> Result<VRFSeed> {
        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        self.headers_db
            .get_vrf_seed_for_block(&id_bhh, &epoch)
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()).into())
    }

    pub fn get_miner_address(&mut self, block_height: u32) -> Result<StandardPrincipalData> {
        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        Ok(self
            .headers_db
            .get_miner_address(&id_bhh, &epoch)
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()))?
            .into())
    }

    pub fn get_miner_spend_winner(&mut self, block_height: u32) -> Result<u128> {
        if block_height == 0 {
            return Ok(0);
        }

        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        Ok(self
            .headers_db
            .get_burnchain_tokens_spent_for_winning_block(&id_bhh, &epoch)
            .ok_or_else(|| {
                InterpreterError::Expect(
                    "FATAL: no winning burnchain token spend record for block".into(),
                )
            })?)
    }

    pub fn get_miner_spend_total(&mut self, block_height: u32) -> Result<u128> {
        if block_height == 0 {
            return Ok(0);
        }

        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        Ok(self
            .headers_db
            .get_burnchain_tokens_spent_for_block(&id_bhh, &epoch)
            .ok_or_else(|| {
                InterpreterError::Expect(
                    "FATAL: no total burnchain token spend record for block".into(),
                )
            })?)
    }

    pub fn get_block_reward(&mut self, block_height: u32) -> Result<Option<u128>> {
        if block_height == 0 {
            return Ok(None);
        }

        let cur_height: u64 = self.get_current_block_height().into();

        // reward for the *child* of this block must have matured, since that determines the
        // streamed tx fee reward portion
        if ((block_height + 1) as u64) + MINER_REWARD_MATURITY >= cur_height {
            return Ok(None);
        }

        let id_bhh = self.get_index_block_header_hash(block_height)?;
        let epoch = self.get_stacks_epoch_for_block(&id_bhh)?;
        let reward: u128 = self
            .headers_db
            .get_tokens_earned_for_block(&id_bhh, &epoch)
            .ok_or_else(|| {
                InterpreterError::Expect("FATAL: matured block has no recorded reward".into())
            })?;

        Ok(Some(reward))
    }

    pub fn get_stx_btc_ops_processed(&mut self) -> Result<u64> {
        Ok(self
            .get_data("vm_pox::stx_btc_ops::processed_blocks")?
            .unwrap_or(0))
    }

    pub fn set_stx_btc_ops_processed(&mut self, processed: u64) -> Result<()> {
        self.put_data("vm_pox::stx_btc_ops::processed_blocks", &processed)
    }
}

// poison-microblock

impl ClarityDatabase<'_> {
    pub fn make_microblock_pubkey_height_key(pubkey_hash: &Hash160) -> String {
        format!("microblock-pubkey-hash::{}", pubkey_hash)
    }

    pub fn make_microblock_poison_key(height: u32) -> String {
        format!("microblock-poison::{}", height)
    }

    pub fn insert_microblock_pubkey_hash_height(
        &mut self,
        pubkey_hash: &Hash160,
        height: u32,
    ) -> Result<()> {
        let key = ClarityDatabase::make_microblock_pubkey_height_key(pubkey_hash);
        let value = format!("{}", &height);
        self.put_data(&key, &value)
    }

    pub fn get_cc_special_cases_handler(&self) -> Option<SpecialCaseHandler> {
        self.store.get_cc_special_cases_handler()
    }

    #[allow(clippy::unnecessary_fallible_conversions)]
    pub fn insert_microblock_poison(
        &mut self,
        height: u32,
        reporter: &StandardPrincipalData,
        seq: u16,
    ) -> Result<()> {
        let key = ClarityDatabase::make_microblock_poison_key(height);
        let value = Value::Tuple(
            TupleData::from_data(vec![
                (
                    ClarityName::try_from("reporter").map_err(|_| {
                        InterpreterError::Expect("BUG: valid string representation".into())
                    })?,
                    Value::Principal(PrincipalData::Standard(reporter.clone())),
                ),
                (
                    ClarityName::try_from("sequence").map_err(|_| {
                        InterpreterError::Expect("BUG: valid string representation".into())
                    })?,
                    Value::UInt(seq as u128),
                ),
            ])
            .map_err(|_| InterpreterError::Expect("BUG: valid tuple representation".into()))?,
        );
        let mut value_bytes = vec![];
        value.serialize_write(&mut value_bytes).map_err(|_| {
            InterpreterError::Expect("BUG: valid tuple representation did not serialize".into())
        })?;

        let value_str = to_hex(&value_bytes);
        self.put_data(&key, &value_str)
    }

    pub fn get_microblock_pubkey_hash_height(
        &mut self,
        pubkey_hash: &Hash160,
    ) -> Result<Option<u32>> {
        let key = ClarityDatabase::make_microblock_pubkey_height_key(pubkey_hash);
        self.get_data(&key)?
            .map(|height_str: String| {
                height_str.parse::<u32>().map_err(|_| {
                    InterpreterError::Expect(
                        "BUG: inserted non-u32 as height of microblock pubkey hash".into(),
                    )
                    .into()
                })
            })
            .transpose()
    }

    /// Returns (who-reported-the-poison-microblock, sequence-of-microblock-fork)
    pub fn get_microblock_poison_report(
        &mut self,
        height: u32,
    ) -> Result<Option<(StandardPrincipalData, u16)>> {
        let key = ClarityDatabase::make_microblock_poison_key(height);
        self.get_data(&key)?
            .map(|reporter_hex_str: String| {
                let reporter_value = Value::try_deserialize_hex_untyped(&reporter_hex_str)
                    .map_err(|_| {
                        InterpreterError::Expect(
                            "BUG: failed to decode serialized poison-microblock reporter".into(),
                        )
                    })?;
                let tuple_data = reporter_value.expect_tuple()?;
                let reporter_value = tuple_data
                    .get("reporter")
                    .map_err(|_| {
                        InterpreterError::Expect(
                            "BUG: poison-microblock report has no 'reporter'".into(),
                        )
                    })?
                    .to_owned();
                let seq_value = tuple_data
                    .get("sequence")
                    .map_err(|_| {
                        InterpreterError::Expect(
                            "BUG: poison-microblock report has no 'sequence'".into(),
                        )
                    })?
                    .to_owned();

                let reporter_principal = reporter_value.expect_principal()?;
                let seq_u128 = seq_value.expect_u128()?;

                let seq: u16 = seq_u128
                    .try_into()
                    .map_err(|_| InterpreterError::Expect("BUG: seq exceeds u16 max".into()))?;
                if let PrincipalData::Standard(principal_data) = reporter_principal {
                    Ok((principal_data, seq))
                } else {
                    Err(InterpreterError::Expect(
                        "BUG: poison-microblock report principal is not a standard principal"
                            .into(),
                    )
                    .into())
                }
            })
            .transpose()
    }
}

// this is used so that things like load_map, load_var, load_nft, etc.
//   will throw NoSuchFoo errors instead of NoSuchContract errors.
fn map_no_contract_as_none<T>(res: Result<Option<T>>) -> Result<Option<T>> {
    res.or_else(|e| match e {
        Error::Unchecked(CheckErrors::NoSuchContract(_)) => Ok(None),
        x => Err(x),
    })
}

// Variable Functions...
impl ClarityDatabase<'_> {
    pub fn create_variable(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
        value_type: TypeSignature,
    ) -> Result<DataVariableMetadata> {
        let variable_data = DataVariableMetadata { value_type };
        let key = ClarityDatabase::make_metadata_key(StoreType::VariableMeta, variable_name);

        self.insert_metadata(contract_identifier, &key, &variable_data)?;
        Ok(variable_data)
    }

    pub fn load_variable(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
    ) -> Result<DataVariableMetadata> {
        let key = ClarityDatabase::make_metadata_key(StoreType::VariableMeta, variable_name);

        map_no_contract_as_none(self.fetch_metadata(contract_identifier, &key))?
            .ok_or(CheckErrors::NoSuchDataVariable(variable_name.to_string()).into())
    }

    #[cfg(any(test, feature = "testing"))]
    pub fn set_variable_unknown_descriptor(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
        value: Value,
    ) -> Result<Value> {
        let descriptor = self.load_variable(contract_identifier, variable_name)?;
        self.set_variable(
            contract_identifier,
            variable_name,
            value,
            &descriptor,
            &StacksEpochId::latest(),
        )
        .map(|data| data.value)
    }

    pub fn set_variable(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
        value: Value,
        variable_descriptor: &DataVariableMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        if !variable_descriptor
            .value_type
            .admits(&self.get_clarity_epoch_version()?, &value)?
        {
            return Err(
                CheckErrors::TypeValueError(variable_descriptor.value_type.clone(), value).into(),
            );
        }

        let key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::Variable,
            variable_name,
        );

        let size = self.put_value_with_size(&key, value, epoch)?;

        Ok(ValueResult {
            value: Value::Bool(true),
            serialized_byte_len: size,
        })
    }

    pub fn lookup_variable_unknown_descriptor(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
        epoch: &StacksEpochId,
    ) -> Result<Value> {
        let descriptor = self.load_variable(contract_identifier, variable_name)?;
        self.lookup_variable(contract_identifier, variable_name, &descriptor, epoch)
    }

    pub fn lookup_variable(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
        variable_descriptor: &DataVariableMetadata,
        epoch: &StacksEpochId,
    ) -> Result<Value> {
        let key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::Variable,
            variable_name,
        );

        let result = self.get_value(&key, &variable_descriptor.value_type, epoch)?;

        match result {
            None => Ok(Value::none()),
            Some(data) => Ok(data.value),
        }
    }

    /// Same as lookup_variable, but returns the byte-size of the looked up
    ///  Clarity value as well as the value.
    pub fn lookup_variable_with_size(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        variable_name: &str,
        variable_descriptor: &DataVariableMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        let key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::Variable,
            variable_name,
        );

        let result = self.get_value(&key, &variable_descriptor.value_type, epoch)?;

        match result {
            None => Ok(ValueResult {
                value: Value::none(),
                serialized_byte_len: *NONE_SERIALIZATION_LEN,
            }),
            Some(data) => Ok(data),
        }
    }
}

// Data Map Functions
impl ClarityDatabase<'_> {
    pub fn create_map(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_type: TypeSignature,
        value_type: TypeSignature,
    ) -> Result<DataMapMetadata> {
        let data = DataMapMetadata {
            key_type,
            value_type,
        };

        let key = ClarityDatabase::make_metadata_key(StoreType::DataMapMeta, map_name);
        self.insert_metadata(contract_identifier, &key, &data)?;

        Ok(data)
    }

    pub fn load_map(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
    ) -> Result<DataMapMetadata> {
        let key = ClarityDatabase::make_metadata_key(StoreType::DataMapMeta, map_name);

        map_no_contract_as_none(self.fetch_metadata(contract_identifier, &key))?
            .ok_or(CheckErrors::NoSuchMap(map_name.to_string()).into())
    }

    pub fn make_key_for_data_map_entry(
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value: &Value,
    ) -> Result<String> {
        Ok(ClarityDatabase::make_key_for_data_map_entry_serialized(
            contract_identifier,
            map_name,
            &key_value.serialize_to_hex()?,
        ))
    }

    fn make_key_for_data_map_entry_serialized(
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value_serialized: &str,
    ) -> String {
        ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::DataMap,
            map_name,
            key_value_serialized,
        )
    }

    pub fn fetch_entry_unknown_descriptor(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value: &Value,
        epoch: &StacksEpochId,
    ) -> Result<Value> {
        let descriptor = self.load_map(contract_identifier, map_name)?;
        self.fetch_entry(contract_identifier, map_name, key_value, &descriptor, epoch)
    }

    /// Returns a Clarity optional type wrapping a found or not found result
    pub fn fetch_entry(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value: &Value,
        map_descriptor: &DataMapMetadata,
        epoch: &StacksEpochId,
    ) -> Result<Value> {
        if !map_descriptor
            .key_type
            .admits(&self.get_clarity_epoch_version()?, key_value)?
        {
            return Err(CheckErrors::TypeValueError(
                map_descriptor.key_type.clone(),
                (*key_value).clone(),
            )
            .into());
        }

        let key =
            ClarityDatabase::make_key_for_data_map_entry(contract_identifier, map_name, key_value)?;

        let stored_type = TypeSignature::new_option(map_descriptor.value_type.clone())?;
        let result = self.get_value(&key, &stored_type, epoch)?;

        match result {
            None => Ok(Value::none()),
            Some(data) => Ok(data.value),
        }
    }

    pub fn fetch_entry_with_size(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value: &Value,
        map_descriptor: &DataMapMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        if !map_descriptor
            .key_type
            .admits(&self.get_clarity_epoch_version()?, key_value)?
        {
            return Err(CheckErrors::TypeValueError(
                map_descriptor.key_type.clone(),
                (*key_value).clone(),
            )
            .into());
        }

        let key_serialized = key_value.serialize_to_hex()?;
        let key = ClarityDatabase::make_key_for_data_map_entry_serialized(
            contract_identifier,
            map_name,
            &key_serialized,
        );

        let stored_type = TypeSignature::new_option(map_descriptor.value_type.clone())?;
        let result = self.get_value(&key, &stored_type, epoch)?;

        match result {
            None => Ok(ValueResult {
                value: Value::none(),
                serialized_byte_len: byte_len_of_serialization(&key_serialized),
            }),
            Some(ValueResult {
                value,
                serialized_byte_len,
            }) => Ok(ValueResult {
                value,
                serialized_byte_len: serialized_byte_len
                    .checked_add(byte_len_of_serialization(&key_serialized))
                    .ok_or_else(|| {
                        InterpreterError::Expect("Overflowed Clarity key/value size".into())
                    })?,
            }),
        }
    }

    pub fn set_entry(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key: Value,
        value: Value,
        map_descriptor: &DataMapMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        self.inner_set_entry(
            contract_identifier,
            map_name,
            key,
            value,
            false,
            map_descriptor,
            epoch,
        )
    }

    pub fn set_entry_unknown_descriptor(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key: Value,
        value: Value,
        epoch: &StacksEpochId,
    ) -> Result<Value> {
        let descriptor = self.load_map(contract_identifier, map_name)?;
        self.set_entry(
            contract_identifier,
            map_name,
            key,
            value,
            &descriptor,
            epoch,
        )
        .map(|data| data.value)
    }

    pub fn insert_entry_unknown_descriptor(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key: Value,
        value: Value,
        epoch: &StacksEpochId,
    ) -> Result<Value> {
        let descriptor = self.load_map(contract_identifier, map_name)?;
        self.insert_entry(
            contract_identifier,
            map_name,
            key,
            value,
            &descriptor,
            epoch,
        )
        .map(|data| data.value)
    }

    pub fn insert_entry(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key: Value,
        value: Value,
        map_descriptor: &DataMapMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        self.inner_set_entry(
            contract_identifier,
            map_name,
            key,
            value,
            true,
            map_descriptor,
            epoch,
        )
    }

    fn data_map_entry_exists(
        &mut self,
        key: &str,
        expected_value: &TypeSignature,
        epoch: &StacksEpochId,
    ) -> Result<bool> {
        match self.get_value(key, expected_value, epoch)? {
            None => Ok(false),
            Some(value) => Ok(value.value != Value::none()),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn inner_set_entry(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value: Value,
        value: Value,
        return_if_exists: bool,
        map_descriptor: &DataMapMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        if !map_descriptor
            .key_type
            .admits(&self.get_clarity_epoch_version()?, &key_value)?
        {
            return Err(
                CheckErrors::TypeValueError(map_descriptor.key_type.clone(), key_value).into(),
            );
        }
        if !map_descriptor
            .value_type
            .admits(&self.get_clarity_epoch_version()?, &value)?
        {
            return Err(
                CheckErrors::TypeValueError(map_descriptor.value_type.clone(), value).into(),
            );
        }

        let key_serialized = key_value.serialize_to_hex()?;
        let key_serialized_byte_len = byte_len_of_serialization(&key_serialized);
        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::DataMap,
            map_name,
            &key_serialized,
        );
        let stored_type = TypeSignature::new_option(map_descriptor.value_type.clone())?;

        if return_if_exists && self.data_map_entry_exists(&key, &stored_type, epoch)? {
            return Ok(ValueResult {
                value: Value::Bool(false),
                serialized_byte_len: key_serialized_byte_len,
            });
        }

        let placed_value = Value::some(value)?;
        let placed_size = self.put_value_with_size(&key, placed_value, epoch)?;

        Ok(ValueResult {
            value: Value::Bool(true),
            serialized_byte_len: key_serialized_byte_len
                .checked_add(placed_size)
                .ok_or_else(|| {
                    InterpreterError::Expect("Overflowed Clarity key/value size".into())
                })?,
        })
    }

    pub fn delete_entry(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        map_name: &str,
        key_value: &Value,
        map_descriptor: &DataMapMetadata,
        epoch: &StacksEpochId,
    ) -> Result<ValueResult> {
        if !map_descriptor
            .key_type
            .admits(&self.get_clarity_epoch_version()?, key_value)?
        {
            return Err(CheckErrors::TypeValueError(
                map_descriptor.key_type.clone(),
                (*key_value).clone(),
            )
            .into());
        }

        let key_serialized = key_value.serialize_to_hex()?;
        let key_serialized_byte_len = byte_len_of_serialization(&key_serialized);
        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::DataMap,
            map_name,
            &key_serialized,
        );
        let stored_type = TypeSignature::new_option(map_descriptor.value_type.clone())?;
        if !self.data_map_entry_exists(&key, &stored_type, epoch)? {
            return Ok(ValueResult {
                value: Value::Bool(false),
                serialized_byte_len: key_serialized_byte_len,
            });
        }

        self.put_value(&key, Value::none(), epoch)?;

        Ok(ValueResult {
            value: Value::Bool(true),
            serialized_byte_len: key_serialized_byte_len
                .checked_add(*NONE_SERIALIZATION_LEN)
                .ok_or_else(|| {
                    InterpreterError::Expect("Overflowed Clarity key/value size".into())
                })?,
        })
    }
}

// Asset Functions

impl ClarityDatabase<'_> {
    pub fn create_fungible_token(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
        total_supply: &Option<u128>,
    ) -> Result<FungibleTokenMetadata> {
        let data = FungibleTokenMetadata {
            total_supply: *total_supply,
        };

        let key = ClarityDatabase::make_metadata_key(StoreType::FungibleTokenMeta, token_name);
        self.insert_metadata(contract_identifier, &key, &data)?;

        // total supply _is_ included in the consensus hash
        let supply_key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::CirculatingSupply,
            token_name,
        );
        self.put_data(&supply_key, &(0_u128))?;

        Ok(data)
    }

    pub fn load_ft(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
    ) -> Result<FungibleTokenMetadata> {
        let key = ClarityDatabase::make_metadata_key(StoreType::FungibleTokenMeta, token_name);

        map_no_contract_as_none(self.fetch_metadata(contract_identifier, &key))?
            .ok_or(CheckErrors::NoSuchFT(token_name.to_string()).into())
    }

    pub fn create_non_fungible_token(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
        key_type: &TypeSignature,
    ) -> Result<NonFungibleTokenMetadata> {
        let data = NonFungibleTokenMetadata {
            key_type: key_type.clone(),
        };
        let key = ClarityDatabase::make_metadata_key(StoreType::NonFungibleTokenMeta, token_name);
        self.insert_metadata(contract_identifier, &key, &data)?;

        Ok(data)
    }

    fn load_nft(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
    ) -> Result<NonFungibleTokenMetadata> {
        let key = ClarityDatabase::make_metadata_key(StoreType::NonFungibleTokenMeta, token_name);

        map_no_contract_as_none(self.fetch_metadata(contract_identifier, &key))?
            .ok_or(CheckErrors::NoSuchNFT(token_name.to_string()).into())
    }

    pub fn checked_increase_token_supply(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
        amount: u128,
        descriptor: &FungibleTokenMetadata,
    ) -> Result<()> {
        let key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::CirculatingSupply,
            token_name,
        );
        let current_supply: u128 = self.get_data(&key)?.ok_or_else(|| {
            InterpreterError::Expect("ERROR: Clarity VM failed to track token supply.".into())
        })?;

        let new_supply = current_supply
            .checked_add(amount)
            .ok_or(RuntimeErrorType::ArithmeticOverflow)?;

        if let Some(total_supply) = descriptor.total_supply {
            if new_supply > total_supply {
                return Err(RuntimeErrorType::SupplyOverflow(new_supply, total_supply).into());
            }
        }

        self.put_data(&key, &new_supply)
    }

    pub fn checked_decrease_token_supply(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
        amount: u128,
    ) -> Result<()> {
        let key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::CirculatingSupply,
            token_name,
        );
        let current_supply: u128 = self.get_data(&key)?.ok_or_else(|| {
            InterpreterError::Expect("ERROR: Clarity VM failed to track token supply.".into())
        })?;

        if amount > current_supply {
            return Err(RuntimeErrorType::SupplyUnderflow(current_supply, amount).into());
        }

        let new_supply = current_supply - amount;

        self.put_data(&key, &new_supply)
    }

    pub fn get_ft_balance(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
        principal: &PrincipalData,
        descriptor: Option<&FungibleTokenMetadata>,
    ) -> Result<u128> {
        if descriptor.is_none() {
            self.load_ft(contract_identifier, token_name)?;
        }

        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::FungibleToken,
            token_name,
            &principal.serialize(),
        );

        let result = self.get_data(&key)?;
        match result {
            None => Ok(0),
            Some(balance) => Ok(balance),
        }
    }

    pub fn set_ft_balance(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
        principal: &PrincipalData,
        balance: u128,
    ) -> Result<()> {
        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::FungibleToken,
            token_name,
            &principal.serialize(),
        );
        self.put_data(&key, &balance)
    }

    pub fn get_ft_supply(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        token_name: &str,
    ) -> Result<u128> {
        let key = ClarityDatabase::make_key_for_trip(
            contract_identifier,
            StoreType::CirculatingSupply,
            token_name,
        );
        let supply = self.get_data(&key)?.ok_or_else(|| {
            InterpreterError::Expect("ERROR: Clarity VM failed to track token supply.".into())
        })?;
        Ok(supply)
    }

    pub fn get_nft_owner(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        asset_name: &str,
        asset: &Value,
        key_type: &TypeSignature,
    ) -> Result<PrincipalData> {
        if !key_type.admits(&self.get_clarity_epoch_version()?, asset)? {
            return Err(CheckErrors::TypeValueError(key_type.clone(), (*asset).clone()).into());
        }

        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::NonFungibleToken,
            asset_name,
            &asset.serialize_to_hex()?,
        );

        let epoch = self.get_clarity_epoch_version()?;
        let value: Option<ValueResult> = self.get_value(
            &key,
            &TypeSignature::new_option(TypeSignature::PrincipalType)
                .map_err(|_| InterpreterError::Expect("Unexpected type failure".into()))?,
            &epoch,
        )?;
        let owner = match value {
            Some(owner) => owner.value.expect_optional()?,
            None => return Err(RuntimeErrorType::NoSuchToken.into()),
        };

        let principal = match owner {
            Some(value) => value.expect_principal()?,
            None => return Err(RuntimeErrorType::NoSuchToken.into()),
        };

        Ok(principal)
    }

    pub fn get_nft_key_type(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        asset_name: &str,
    ) -> Result<TypeSignature> {
        let descriptor = self.load_nft(contract_identifier, asset_name)?;
        Ok(descriptor.key_type)
    }

    pub fn set_nft_owner(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        asset_name: &str,
        asset: &Value,
        principal: &PrincipalData,
        key_type: &TypeSignature,
        epoch: &StacksEpochId,
    ) -> Result<()> {
        if !key_type.admits(&self.get_clarity_epoch_version()?, asset)? {
            return Err(CheckErrors::TypeValueError(key_type.clone(), (*asset).clone()).into());
        }

        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::NonFungibleToken,
            asset_name,
            &asset.serialize_to_hex()?,
        );

        let value = Value::some(Value::Principal(principal.clone()))?;
        self.put_value(&key, value, epoch)?;

        Ok(())
    }

    pub fn burn_nft(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        asset_name: &str,
        asset: &Value,
        key_type: &TypeSignature,
        epoch: &StacksEpochId,
    ) -> Result<()> {
        if !key_type.admits(&self.get_clarity_epoch_version()?, asset)? {
            return Err(CheckErrors::TypeValueError(key_type.clone(), (*asset).clone()).into());
        }

        let key = ClarityDatabase::make_key_for_quad(
            contract_identifier,
            StoreType::NonFungibleToken,
            asset_name,
            &asset.serialize_to_hex()?,
        );

        self.put_value(&key, Value::none(), epoch)?;
        Ok(())
    }
}

// load/store STX token state and account nonces
impl<'a> ClarityDatabase<'a> {
    fn make_key_for_account(principal: &PrincipalData, data: StoreType) -> String {
        format!("vm-account::{}::{}", principal, data as u8)
    }

    pub fn make_key_for_account_balance(principal: &PrincipalData) -> String {
        ClarityDatabase::make_key_for_account(principal, StoreType::STXBalance)
    }

    pub fn make_key_for_account_nonce(principal: &PrincipalData) -> String {
        ClarityDatabase::make_key_for_account(principal, StoreType::Nonce)
    }

    pub fn make_key_for_account_stx_locked(principal: &PrincipalData) -> String {
        ClarityDatabase::make_key_for_account(principal, StoreType::PoxSTXLockup)
    }

    pub fn make_key_for_account_unlock_height(principal: &PrincipalData) -> String {
        ClarityDatabase::make_key_for_account(principal, StoreType::PoxUnlockHeight)
    }

    pub fn get_stx_balance_snapshot<'conn>(
        &'conn mut self,
        principal: &PrincipalData,
    ) -> Result<STXBalanceSnapshot<'a, 'conn>> {
        let stx_balance = self.get_account_stx_balance(principal)?;
        let cur_burn_height = u64::from(self.get_current_burnchain_block_height()?);

        test_debug!("Balance of {} (raw={},locked={},unlock-height={},current-height={}) is {} (has_unlockable_tokens_at_burn_block={})",
            principal,
            stx_balance.amount_unlocked(),
            stx_balance.amount_locked(),
            stx_balance.unlock_height(),
            cur_burn_height,
            stx_balance.get_available_balance_at_burn_block(cur_burn_height, self.get_v1_unlock_height(), self.get_v2_unlock_height()?, self.get_v3_unlock_height()?)?,
            stx_balance.has_unlockable_tokens_at_burn_block(cur_burn_height, self.get_v1_unlock_height(), self.get_v2_unlock_height()?, self.get_v3_unlock_height()?));

        Ok(STXBalanceSnapshot::new(
            principal,
            stx_balance,
            cur_burn_height,
            self,
        ))
    }

    pub fn get_stx_balance_snapshot_genesis<'conn>(
        &'conn mut self,
        principal: &PrincipalData,
    ) -> Result<STXBalanceSnapshot<'a, 'conn>> {
        let stx_balance = self.get_account_stx_balance(principal)?;
        let cur_burn_height = 0;

        test_debug!("Balance of {} (raw={},locked={},unlock-height={},current-height={}) is {} (has_unlockable_tokens_at_burn_block={})",
            principal,
            stx_balance.amount_unlocked(),
            stx_balance.amount_locked(),
            stx_balance.unlock_height(),
            cur_burn_height,
            stx_balance.get_available_balance_at_burn_block(cur_burn_height, self.get_v1_unlock_height(), self.get_v2_unlock_height()?, self.get_v3_unlock_height()?)?,
            stx_balance.has_unlockable_tokens_at_burn_block(cur_burn_height, self.get_v1_unlock_height(), self.get_v2_unlock_height()?, self.get_v3_unlock_height()?));

        Ok(STXBalanceSnapshot::new(
            principal,
            stx_balance,
            cur_burn_height,
            self,
        ))
    }

    pub fn get_account_stx_balance(&mut self, principal: &PrincipalData) -> Result<STXBalance> {
        let key = ClarityDatabase::make_key_for_account_balance(principal);
        debug!("Fetching account balance"; "principal" => %principal.to_string());
        let result = self.get_data(&key)?;
        Ok(result.unwrap_or_default())
    }

    pub fn get_account_nonce(&mut self, principal: &PrincipalData) -> Result<u64> {
        let key = ClarityDatabase::make_key_for_account_nonce(principal);
        let result = self.get_data(&key)?;
        Ok(result.unwrap_or_default())
    }

    pub fn set_account_nonce(&mut self, principal: &PrincipalData, nonce: u64) -> Result<()> {
        let key = ClarityDatabase::make_key_for_account_nonce(principal);
        self.put_data(&key, &nonce)
    }
}

// access burnchain state
impl ClarityDatabase<'_> {
    pub fn get_burn_block_height(&self, sortition_id: &SortitionId) -> Option<u32> {
        self.burn_state_db.get_burn_block_height(sortition_id)
    }

    /// This function obtains the stacks epoch version, which is based on the burn block height.
    /// Valid epochs include stacks 1.0, 2.0, 2.05, and so on.
    pub fn get_stacks_epoch(&self, height: u32) -> Option<StacksEpoch> {
        self.burn_state_db.get_stacks_epoch(height)
    }

    pub fn get_stacks_epoch_for_block(&self, id_bhh: &StacksBlockId) -> Result<StacksEpochId> {
        let burn_block = self.get_burnchain_block_height(id_bhh).ok_or_else(|| {
            InterpreterError::Expect(format!(
                "FATAL: no burnchain block height found for Stacks block {}",
                id_bhh
            ))
        })?;
        let epoch = self
            .get_stacks_epoch(burn_block)
            .ok_or_else(|| InterpreterError::Expect("Failed to get block data.".into()))?;
        Ok(epoch.epoch_id)
    }
}
