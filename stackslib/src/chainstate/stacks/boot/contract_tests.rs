use std::collections::{HashMap, VecDeque};

use clarity::vm::analysis::arithmetic_checker::ArithmeticOnlyChecker;
use clarity::vm::ast::ASTRules;
use clarity::vm::clarity::{ClarityConnection, TransactionConnection};
use clarity::vm::contexts::OwnedEnvironment;
use clarity::vm::contracts::Contract;
use clarity::vm::costs::CostOverflowingMath;
use clarity::vm::database::*;
use clarity::vm::errors::{
    CheckErrors, Error, IncomparableError, InterpreterError, InterpreterResult as Result,
    RuntimeErrorType,
};
use clarity::vm::eval;
use clarity::vm::representations::SymbolicExpression;
use clarity::vm::test_util::{execute, symbols_from_values, TEST_BURN_STATE_DB, TEST_HEADER_DB};
use clarity::vm::tooling::mem_type_check;
use clarity::vm::types::Value::Response;
use clarity::vm::types::{
    OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData, StandardPrincipalData,
    TupleData, TupleTypeSignature, TypeSignature, Value, NONE,
};
use clarity::vm::version::ClarityVersion;
use lazy_static::lazy_static;
use stacks_common::address::AddressHashMode;
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, SortitionId, StacksAddress, StacksBlockId, VRFSeed,
};
use stacks_common::util::hash::{to_hex, Sha256Sum, Sha512Trunc256Sum};

use super::SIGNERS_MAX_LIST_SIZE;
use crate::burnchains::{Burnchain, PoxConstants};
use crate::chainstate::burn::ConsensusHash;
use crate::chainstate::stacks::address::PoxAddress;
use crate::chainstate::stacks::boot::{
    BOOT_CODE_COST_VOTING_TESTNET as BOOT_CODE_COST_VOTING, BOOT_CODE_POX_TESTNET,
    POX_2_TESTNET_CODE,
};
use crate::chainstate::stacks::db::{MinerPaymentSchedule, StacksHeaderInfo};
use crate::chainstate::stacks::index::{ClarityMarfTrieId, MarfTrieId, TrieMerkleProof};
use crate::chainstate::stacks::{C32_ADDRESS_VERSION_TESTNET_SINGLESIG, *};
use crate::clarity_vm::clarity::{ClarityBlockConnection, Error as ClarityError};
use crate::clarity_vm::database::marf::{MarfedKV, WritableMarfStore};
use crate::core::{
    StacksEpoch, StacksEpochId, BITCOIN_REGTEST_FIRST_BLOCK_HASH,
    BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT, BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP,
    FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH, PEER_VERSION_EPOCH_1_0,
    POX_REWARD_CYCLE_LENGTH, POX_TESTNET_CYCLE_LENGTH,
};
use crate::util_lib::boot::{boot_code_addr, boot_code_id};
use crate::util_lib::db::{DBConn, FromRow};

const USTX_PER_HOLDER: u128 = 1_000_000;

lazy_static! {
    pub static ref FIRST_INDEX_BLOCK_HASH: StacksBlockId = StacksBlockHeader::make_index_block_hash(
        &FIRST_BURNCHAIN_CONSENSUS_HASH,
        &FIRST_STACKS_BLOCK_HASH
    );
    pub static ref POX_CONTRACT_TESTNET: QualifiedContractIdentifier = boot_code_id("pox", false);
    pub static ref POX_2_CONTRACT_TESTNET: QualifiedContractIdentifier =
        boot_code_id("pox-2", false);
    pub static ref COST_VOTING_CONTRACT_TESTNET: QualifiedContractIdentifier =
        boot_code_id("cost-voting", false);
    pub static ref USER_KEYS: Vec<StacksPrivateKey> =
        (0..50).map(|_| StacksPrivateKey::new()).collect();
    pub static ref POX_ADDRS: Vec<Value> = (0..50u64)
        .map(|ix| execute(&format!(
            "{{ version: 0x00, hashbytes: 0x000000000000000000000000{} }}",
            &to_hex(&ix.to_le_bytes())
        )))
        .collect();
    pub static ref MINER_KEY: StacksPrivateKey = StacksPrivateKey::new();
    pub static ref MINER_ADDR: StacksAddress = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&MINER_KEY.clone())],
    )
    .unwrap();
    static ref LIQUID_SUPPLY: u128 = USTX_PER_HOLDER * (POX_ADDRS.len() as u128);
    static ref MIN_THRESHOLD: u128 = *LIQUID_SUPPLY / super::test::TESTNET_STACKING_THRESHOLD_25;
}

pub struct ClarityTestSim {
    marf: MarfedKV,
    pub block_height: u64,
    pub tenure_height: u64,
    fork: u64,
    /// This vec specifies the transitions for each epoch.
    /// It is a list of heights at which the simulated chain transitions
    /// first to Epoch 2.0, then to Epoch 2.05, then to Epoch 2.1, etc. If the Epoch 2.0 transition
    /// is set to 0, Epoch 1.0 will be skipped. Otherwise, the simulated chain will
    /// begin in Epoch 1.0.
    pub epoch_bounds: Vec<u64>,
}

pub struct TestSimHeadersDB {
    height: u64,
}

pub struct TestSimBurnStateDB {
    /// This vec specifies the transitions for each epoch.
    /// It is a list of heights at which the simulated chain transitions
    /// first to Epoch 2.0, then to Epoch 2.05, then to Epoch 2.1, etc. If the Epoch 2.0 transition
    /// is set to 0, Epoch 1.0 will be skipped. Otherwise, the simulated chain will
    /// begin in Epoch 1.0.
    epoch_bounds: Vec<u64>,
    pox_constants: PoxConstants,
    height: u32,
}

impl ClarityTestSim {
    pub fn new() -> ClarityTestSim {
        let mut marf = MarfedKV::temporary();
        {
            let mut store = marf.begin(
                &StacksBlockId::sentinel(),
                &StacksBlockId(test_sim_height_to_hash(0, 0)),
            );

            let mut db = store.as_clarity_db(&TEST_HEADER_DB, &TEST_BURN_STATE_DB);
            db.initialize();

            let mut owned_env = OwnedEnvironment::new_toplevel(db);

            for user_key in USER_KEYS.iter() {
                owned_env.stx_faucet(
                    &StandardPrincipalData::from(user_key).into(),
                    USTX_PER_HOLDER,
                );
            }
            store.test_commit();
        }

        ClarityTestSim {
            marf,
            block_height: 0,
            tenure_height: 0,
            fork: 0,
            epoch_bounds: vec![0, u64::MAX],
        }
    }

    pub fn burn_block_height(&self) -> u64 {
        self.tenure_height + 100
    }

    pub fn execute_next_block_as_conn_with_tenure<F, R>(&mut self, new_tenure: bool, f: F) -> R
    where
        F: FnOnce(&mut ClarityBlockConnection) -> R,
    {
        let r = {
            let mut store = self.marf.begin(
                &StacksBlockId(test_sim_height_to_hash(self.block_height, self.fork)),
                &StacksBlockId(test_sim_height_to_hash(self.block_height + 1, self.fork)),
            );

            self.block_height += 1;
            if new_tenure {
                self.tenure_height += 1;
            }

            let headers_db = TestSimHeadersDB {
                height: self.block_height,
            };
            let burn_db = TestSimBurnStateDB {
                epoch_bounds: self.epoch_bounds.clone(),
                pox_constants: PoxConstants::test_default(),
                height: (self.tenure_height + 100).try_into().unwrap(),
            };

            let cur_epoch = Self::check_and_bump_epoch(&mut store, &headers_db, &burn_db);

            let mut db = store.as_clarity_db(&headers_db, &burn_db);
            if cur_epoch.clarity_uses_tip_burn_block() {
                db.begin();
                db.set_tenure_height(self.tenure_height as u32)
                    .expect("FAIL: unable to set tenure height in Clarity database");
                db.commit()
                    .expect("FAIL: unable to commit tenure height in Clarity database");
            }

            let mut block_conn =
                ClarityBlockConnection::new_test_conn(store, &headers_db, &burn_db, cur_epoch);
            let r = f(&mut block_conn);
            block_conn.commit_block();

            r
        };

        r
    }

    pub fn execute_next_block_as_conn<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut ClarityBlockConnection) -> R,
    {
        self.execute_next_block_as_conn_with_tenure(true, f)
    }

    pub fn execute_next_block_with_tenure<F, R>(&mut self, new_tenure: bool, f: F) -> R
    where
        F: FnOnce(&mut OwnedEnvironment) -> R,
    {
        let mut store = self.marf.begin(
            &StacksBlockId(test_sim_height_to_hash(self.block_height, self.fork)),
            &StacksBlockId(test_sim_height_to_hash(self.block_height + 1, self.fork)),
        );

        self.block_height += 1;
        if new_tenure {
            self.tenure_height += 1;
        }

        let r = {
            let headers_db = TestSimHeadersDB {
                height: self.block_height,
            };
            let burn_db = TestSimBurnStateDB {
                epoch_bounds: self.epoch_bounds.clone(),
                pox_constants: PoxConstants::test_default(),
                height: (self.tenure_height + 100).try_into().unwrap(),
            };

            let cur_epoch = Self::check_and_bump_epoch(&mut store, &headers_db, &burn_db);
            debug!("Execute block in epoch {}", &cur_epoch);

            let mut db = store.as_clarity_db(&headers_db, &burn_db);
            if cur_epoch.clarity_uses_tip_burn_block() {
                db.begin();
                db.set_tenure_height(self.tenure_height as u32)
                    .expect("FAIL: unable to set tenure height in Clarity database");
                db.commit()
                    .expect("FAIL: unable to commit tenure height in Clarity database");
            }
            let mut owned_env = OwnedEnvironment::new_toplevel(db);
            f(&mut owned_env)
        };

        store.test_commit();

        r
    }

    pub fn execute_next_block<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut OwnedEnvironment) -> R,
    {
        self.execute_next_block_with_tenure(true, f)
    }

    fn check_and_bump_epoch(
        store: &mut WritableMarfStore,
        headers_db: &TestSimHeadersDB,
        burn_db: &dyn BurnStateDB,
    ) -> StacksEpochId {
        let mut clarity_db = store.as_clarity_db(headers_db, burn_db);
        clarity_db.begin();
        let parent_epoch = clarity_db.get_clarity_epoch_version().unwrap();
        let sortition_epoch = clarity_db
            .get_stacks_epoch(headers_db.height as u32)
            .unwrap()
            .epoch_id;

        if parent_epoch != sortition_epoch {
            debug!("Set epoch to {}", &sortition_epoch);
            clarity_db
                .set_clarity_epoch_version(sortition_epoch)
                .unwrap();
        }

        clarity_db.commit().unwrap();
        sortition_epoch
    }

    pub fn execute_block_as_fork<F, R>(&mut self, parent_height: u64, f: F) -> R
    where
        F: FnOnce(&mut OwnedEnvironment) -> R,
    {
        let mut store = self.marf.begin(
            &StacksBlockId(test_sim_height_to_hash(parent_height, self.fork)),
            &StacksBlockId(test_sim_height_to_hash(parent_height + 1, self.fork + 1)),
        );

        let r = {
            let headers_db = TestSimHeadersDB {
                height: parent_height + 1,
            };

            Self::check_and_bump_epoch(&mut store, &headers_db, &NULL_BURN_STATE_DB);

            let db = store.as_clarity_db(&headers_db, &TEST_BURN_STATE_DB);
            let mut owned_env = OwnedEnvironment::new_toplevel(db);

            f(&mut owned_env)
        };

        store.test_commit();
        self.block_height = parent_height + 1;
        self.tenure_height = parent_height + 1;
        self.fork += 1;

        r
    }
}

pub fn test_sim_height_to_hash(burn_height: u64, fork: u64) -> [u8; 32] {
    let mut out = [0; 32];
    out[0..8].copy_from_slice(&burn_height.to_le_bytes());
    out[8..16].copy_from_slice(&fork.to_le_bytes());
    out
}

pub fn test_sim_hash_to_height(in_bytes: &[u8; 32]) -> Option<u64> {
    if &in_bytes[16..] != &[0; 16] {
        None
    } else {
        let mut bytes = [0; 8];
        bytes.copy_from_slice(&in_bytes[0..8]);
        Some(u64::from_le_bytes(bytes))
    }
}

pub fn test_sim_hash_to_fork(in_bytes: &[u8; 32]) -> Option<u64> {
    if &in_bytes[16..] != &[0; 16] {
        None
    } else {
        let mut bytes = [0; 8];
        bytes.copy_from_slice(&in_bytes[8..16]);
        Some(u64::from_le_bytes(bytes))
    }
}

#[cfg(test)]
fn check_arithmetic_only(contract: &str, version: ClarityVersion) {
    let analysis = mem_type_check(contract, version, StacksEpochId::latest())
        .unwrap()
        .1;
    ArithmeticOnlyChecker::run(&analysis).expect("Should pass arithmetic checks");
}

#[test]
fn cost_contract_is_arithmetic_only() {
    use crate::chainstate::stacks::boot::BOOT_CODE_COSTS;
    check_arithmetic_only(BOOT_CODE_COSTS, ClarityVersion::Clarity1);
}

#[test]
fn cost_2_contract_is_arithmetic_only() {
    use crate::chainstate::stacks::boot::BOOT_CODE_COSTS_2;
    check_arithmetic_only(BOOT_CODE_COSTS_2, ClarityVersion::Clarity2);
}

impl BurnStateDB for TestSimBurnStateDB {
    fn get_tip_burn_block_height(&self) -> Option<u32> {
        Some(self.height)
    }

    fn get_tip_sortition_id(&self) -> Option<SortitionId> {
        panic!("Not implemented in TestSim");
    }

    fn get_burn_block_height(&self, sortition_id: &SortitionId) -> Option<u32> {
        panic!("Not implemented in TestSim");
    }

    fn get_burn_header_hash(
        &self,
        height: u32,
        sortition_id: &SortitionId,
    ) -> Option<BurnchainHeaderHash> {
        // generate burnchain header hash for height if the sortition ID is a valid test-sim
        // sortition ID
        if height >= self.height {
            None
        } else {
            match (
                test_sim_hash_to_height(&sortition_id.0),
                test_sim_hash_to_fork(&sortition_id.0),
            ) {
                (Some(_ht), Some(fork)) => Some(BurnchainHeaderHash(test_sim_height_to_hash(
                    height.into(),
                    fork,
                ))),
                _ => None,
            }
        }
    }

    fn get_sortition_id_from_consensus_hash(
        &self,
        consensus_hash: &ConsensusHash,
    ) -> Option<SortitionId> {
        // consensus hashes are constructed as the leading 20 bytes of the stacks block ID from
        // whence it came.
        let mut bytes = [0u8; 32];
        bytes[0..20].copy_from_slice(&consensus_hash.0);
        Some(SortitionId(bytes))
    }

    fn get_stacks_epoch(&self, height: u32) -> Option<StacksEpoch> {
        let epoch_begin_index = match self.epoch_bounds.binary_search(&(height as u64)) {
            Ok(index) => index,
            Err(index) => {
                if index == 0 {
                    return Some(StacksEpoch {
                        start_height: 0,
                        end_height: self.epoch_bounds[0],
                        epoch_id: StacksEpochId::Epoch10,
                        block_limit: ExecutionCost::max_value(),
                        network_epoch: PEER_VERSION_EPOCH_1_0,
                    });
                } else {
                    index - 1
                }
            }
        };

        let epoch_id = match epoch_begin_index {
            0 => StacksEpochId::Epoch20,
            1 => StacksEpochId::Epoch2_05,
            2 => StacksEpochId::Epoch21,
            3 => StacksEpochId::Epoch22,
            4 => StacksEpochId::Epoch23,
            5 => StacksEpochId::Epoch24,
            6 => StacksEpochId::Epoch25,
            7 => StacksEpochId::Epoch30,
            _ => panic!("Invalid epoch index"),
        };

        Some(StacksEpoch {
            start_height: self.epoch_bounds[epoch_begin_index],
            end_height: self
                .epoch_bounds
                .get(epoch_begin_index + 1)
                .cloned()
                .unwrap_or(u64::MAX),
            epoch_id,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        })
    }

    fn get_burn_start_height(&self) -> u32 {
        0
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
        self.pox_constants.prepare_length
    }

    fn get_pox_reward_cycle_length(&self) -> u32 {
        self.pox_constants.reward_cycle_length
    }

    fn get_pox_rejection_fraction(&self) -> u64 {
        self.pox_constants.pox_rejection_fraction
    }

    fn get_stacks_epoch_by_epoch_id(&self, _epoch_id: &StacksEpochId) -> Option<StacksEpoch> {
        self.get_stacks_epoch(0)
    }
    fn get_pox_payout_addrs(
        &self,
        height: u32,
        sortition_id: &SortitionId,
    ) -> Option<(Vec<TupleData>, u128)> {
        if let Some(_) = self.get_burn_header_hash(height, sortition_id) {
            let first_block = self.get_burn_start_height();
            let prepare_len = self.get_pox_prepare_length();
            let rc_len = self.get_pox_reward_cycle_length();
            if PoxConstants::static_is_in_prepare_phase(
                first_block.into(),
                rc_len.into(),
                prepare_len.into(),
                height.into(),
            ) {
                Some((
                    vec![PoxAddress::standard_burn_address(false)
                        .as_clarity_tuple()
                        .unwrap()],
                    123,
                ))
            } else {
                Some((
                    vec![
                        PoxAddress::standard_burn_address(false)
                            .as_clarity_tuple()
                            .unwrap(),
                        PoxAddress::standard_burn_address(false)
                            .as_clarity_tuple()
                            .unwrap(),
                    ],
                    123,
                ))
            }
        } else {
            None
        }
    }

    fn get_ast_rules(&self, _block_height: u32) -> ASTRules {
        ASTRules::PrecheckSize
    }
}

#[cfg(test)]
impl HeadersDB for TestSimHeadersDB {
    fn get_burn_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
    ) -> Option<BurnchainHeaderHash> {
        if *id_bhh == *FIRST_INDEX_BLOCK_HASH {
            Some(BurnchainHeaderHash::from_hex(BITCOIN_REGTEST_FIRST_BLOCK_HASH).unwrap())
        } else {
            if self.get_burn_block_height_for_block(id_bhh).is_none() {
                return None;
            }
            Some(BurnchainHeaderHash(id_bhh.0.clone()))
        }
    }

    fn get_vrf_seed_for_block(
        &self,
        _bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<VRFSeed> {
        None
    }

    fn get_consensus_hash_for_block(
        &self,
        bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<ConsensusHash> {
        // capture the first 20 bytes of the block ID, which in this case captures the height and
        // fork ID.
        let mut bytes_20 = [0u8; 20];
        bytes_20.copy_from_slice(&bhh.0[0..20]);
        Some(ConsensusHash(bytes_20))
    }

    fn get_stacks_block_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<BlockHeaderHash> {
        if *id_bhh == *FIRST_INDEX_BLOCK_HASH {
            Some(FIRST_STACKS_BLOCK_HASH)
        } else {
            if self.get_burn_block_height_for_block(id_bhh).is_none() {
                return None;
            }
            Some(BlockHeaderHash(id_bhh.0.clone()))
        }
    }

    fn get_burn_block_time_for_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: Option<&StacksEpochId>,
    ) -> Option<u64> {
        if *id_bhh == *FIRST_INDEX_BLOCK_HASH {
            Some(BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP as u64)
        } else {
            let burn_block_height = self.get_burn_block_height_for_block(id_bhh)? as u64;
            Some(
                BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP as u64 + burn_block_height
                    - BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT,
            )
        }
    }

    fn get_stacks_block_time_for_block(&self, id_bhh: &StacksBlockId) -> Option<u64> {
        let block_height = test_sim_hash_to_height(&id_bhh.0)?;
        Some(1713799973 + block_height)
    }

    fn get_burn_block_height_for_block(&self, id_bhh: &StacksBlockId) -> Option<u32> {
        if *id_bhh == *FIRST_INDEX_BLOCK_HASH {
            Some(BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT as u32)
        } else {
            let input_height = test_sim_hash_to_height(&id_bhh.0)?;
            if input_height > self.height {
                eprintln!("{} > {}", input_height, self.height);
                None
            } else {
                Some(
                    (BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT + input_height)
                        .try_into()
                        .unwrap(),
                )
            }
        }
    }

    fn get_miner_address(
        &self,
        _id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<StacksAddress> {
        Some(MINER_ADDR.clone())
    }

    fn get_burnchain_tokens_spent_for_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<u128> {
        // if the block is defined at all, then return a constant
        self.get_burn_block_height_for_block(id_bhh).map(|_| 2000)
    }

    fn get_burnchain_tokens_spent_for_winning_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<u128> {
        // if the block is defined at all, then return a constant
        self.get_burn_block_height_for_block(id_bhh).map(|_| 1000)
    }

    fn get_tokens_earned_for_block(
        &self,
        id_bhh: &StacksBlockId,
        _epoch: &StacksEpochId,
    ) -> Option<u128> {
        // if the block is defined at all, then return a constant
        self.get_burn_block_height_for_block(id_bhh).map(|_| 3000)
    }

    fn get_stacks_height_for_tenure_height(
        &self,
        _tip: &StacksBlockId,
        tenure_height: u32,
    ) -> Option<u32> {
        Some(tenure_height)
    }
}

#[test]
fn pox_2_contract_caller_units() {
    let mut sim = ClarityTestSim::new();
    sim.epoch_bounds = vec![0, 1, 2];
    let delegator = StacksPrivateKey::new();

    let expected_unlock_height = POX_TESTNET_CYCLE_LENGTH * 4;

    // execute past 2.1 epoch initialization
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});

    sim.execute_next_block(|env| {
        env.initialize_versioned_contract(
            POX_2_CONTRACT_TESTNET.clone(),
            ClarityVersion::Clarity2,
            &POX_2_TESTNET_CODE,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap()
    });

    let cc = boot_code_id("stack-through", false);

    sim.execute_next_block(|env| {
        env.initialize_contract(cc.clone(),
                                "(define-public (cc-stack-stx (amount-ustx uint)
                                                           (pox-addr (tuple (version (buff 1)) (hashbytes (buff 32))))
                                                           (start-burn-ht uint)
                                                           (lock-period uint))
                                   (contract-call? .pox-2 stack-stx amount-ustx pox-addr start-burn-ht lock-period))",
                                None,
                                ASTRules::PrecheckSize)
            .unwrap();

        let burn_height = env.eval_raw("burn-block-height").unwrap().0;

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                cc.clone(),
                "cc-stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 9)".to_string(),
            "The stack-through contract isn't an allowed caller for POX_ADDR[1] in the PoX2 contract",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "allow-contract-caller",
                &symbols_from_values(vec![
                    cc.clone().into(),
                    Value::none(),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string(),
            "USER[0] should be able to add stack-through as a contract caller in the PoX2 contract",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                cc.clone(),
                "cc-stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[0].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[0]),
                Value::UInt(USTX_PER_HOLDER),
                Value::UInt(expected_unlock_height)
            )),
            "The stack-through contract should be an allowed caller for POX_ADDR[0] in the PoX2 contract",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "disallow-contract-caller",
                &symbols_from_values(vec![
                    cc.clone().into(),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string(),
            "USER[0] should be able to remove stack-through as a contract caller in the PoX2 contract",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                cc.clone(),
                "cc-stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 9)".to_string(),
            "After revocation, stack-through shouldn't be an allowed caller for User 0 in the PoX2 contract",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                cc.clone(),
                "cc-stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[2].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 9)".to_string(),
            "After revocation, stack-through still shouldn't be an allowed caller for User 1 in the PoX2 contract",
        );

        let until_height = Value::UInt(burn_height.clone().expect_u128().unwrap() + 1);

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "allow-contract-caller",
                &symbols_from_values(vec![
                    cc.clone().into(),
                    Value::some(until_height).unwrap(),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string(),
            "User1 should be able to set an 'until-height' on a contract-caller allowance",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                cc.clone(),
                "cc-stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[0].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[1]),
                Value::UInt(USTX_PER_HOLDER),
                Value::UInt(expected_unlock_height)
            )),
            "The stack-through contract should be an allowed caller for User1 in the PoX2 contract",
        );
    });

    sim.execute_next_block(|env| {
        let burn_height = env.eval_raw("burn-block-height").unwrap().0;

        // the contract caller allowance should now have expired:
        //   (err 9) indicates the contract caller check failed
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                cc.clone(),
                "cc-stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[2].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 9)".to_string(),
            "After the `until-height` is reached, stack-through shouldn't be an allowed caller for User1",
        );
    });
}

#[test]
fn pox_2_lock_extend_units() {
    let mut sim = ClarityTestSim::new();
    sim.epoch_bounds = vec![0, 1, 2];
    let delegator = StacksPrivateKey::new();

    let reward_cycle_len = 5;
    let expected_user_1_unlock = 4 * reward_cycle_len + 9 * reward_cycle_len;

    // execute past 2.1 epoch initialization
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});

    sim.execute_next_block(|env| {
        env.initialize_versioned_contract(
            POX_2_CONTRACT_TESTNET.clone(),
            ClarityVersion::Clarity2,
            &POX_2_TESTNET_CODE,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        env.execute_in_env(boot_code_addr(false).into(), None, None, |env| {
            env.execute_contract(
                POX_2_CONTRACT_TESTNET.deref(),
                "set-burnchain-parameters",
                &symbols_from_values(vec![
                    Value::UInt(0),
                    Value::UInt(1),
                    Value::UInt(reward_cycle_len),
                    Value::UInt(25),
                    Value::UInt(0),
                ]),
                false,
            )
        })
        .unwrap();
    });

    sim.execute_next_block(|env| {
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-extend",
                &symbols_from_values(vec![
                    Value::UInt(3),
                    POX_ADDRS[0].clone(),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 26)".to_string(),
            "Should not be able to call stack-extend before locked",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(2 * USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "Should be able to delegate",
        );

        let burn_height = env.eval_raw("burn-block-height").unwrap().0;
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[0]),
                Value::UInt(*MIN_THRESHOLD - 1),
                Value::UInt(3 * reward_cycle_len)
            )),
            "delegate-stack-stx should work okay",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-extend",
                &symbols_from_values(vec![
                    Value::UInt(3),
                    POX_ADDRS[0].clone(),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 20)".to_string(),
            "Cannot stack-extend while delegating",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[1]),
                Value::UInt(USTX_PER_HOLDER),
                Value::UInt(4 * reward_cycle_len)
            )),
            "User1 should be able to stack-stx",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-extend",
                &symbols_from_values(vec![
                    Value::UInt(10),
                    POX_ADDRS[2].clone(),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 2)".to_string(),
            "Should not be able to stack-extend to over 12 cycles in the future",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-extend",
                &symbols_from_values(vec![
                    Value::UInt(9),
                    POX_ADDRS[2].clone(),
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[1]),
                Value::UInt(expected_user_1_unlock),
            )),
            "Should be able to stack-extend to exactly 12 cycles in the future",
        );

        // check that entries exist for each cycle stacked
        for cycle in 0..20 {
            eprintln!("Cycle number = {}", cycle);
            let empty_set = cycle < 1 || cycle >= 13;
            let expected = if empty_set {
                "(u0 u0)"
            } else {
                "(u1000000 u1)"
            };
            assert_eq!(
                env.eval_read_only(
                    &POX_2_CONTRACT_TESTNET,
                    &format!("(list (default-to u0 (get total-ustx (map-get? reward-cycle-total-stacked {{ reward-cycle: u{} }})))
                                    (default-to u0 (get len (map-get? reward-cycle-pox-address-list-len {{ reward-cycle: u{} }}))))",
                             cycle, cycle))
                    .unwrap()
                    .0
                    .to_string(),
                expected
            );
            if !empty_set {
                let expected_pox_addr = if cycle > 3 {
                    &POX_ADDRS[2]
                } else {
                    &POX_ADDRS[1]
                };
                let expected_stacker = Value::from(&USER_KEYS[1]);
                assert_eq!(
                    env.eval_read_only(
                        &POX_2_CONTRACT_TESTNET,
                        &format!("(unwrap-panic (map-get? reward-cycle-pox-address-list {{ reward-cycle: u{}, index: u0 }}))",
                                 cycle))
                        .unwrap()
                        .0,
                    execute(&format!(
                        "{{ pox-addr: {}, total-ustx: u{}, stacker: (some '{}) }}",
                        expected_pox_addr,
                        1_000_000,
                        &expected_stacker,
                    ))
                );
            }
        }
    });

    // now, advance the chain until User1 is unlocked, and try to stack-extend
    for _i in 0..expected_user_1_unlock {
        sim.execute_next_block(|_| {});
    }

    sim.execute_next_block(|env| {
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-extend",
                &symbols_from_values(vec![Value::UInt(3), POX_ADDRS[0].clone(),])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 26)".to_string(),
            "Should not be able to call stack-extend after lock expired",
        );
    });
}

#[test]
fn pox_2_delegate_extend_units() {
    let mut sim = ClarityTestSim::new();
    sim.epoch_bounds = vec![0, 1, 2];
    let delegator = StacksPrivateKey::new();

    // execute past 2.1 epoch initialization
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});

    sim.execute_next_block_as_conn(|conn| {
        test_deploy_smart_contract(
            conn,
            &POX_2_CONTRACT_TESTNET,
            &POX_2_TESTNET_CODE,
            ClarityVersion::Clarity2,
        )
        .unwrap();

        // set burnchain params based on old testnet settings (< 2.0.11.0)
        conn.as_transaction(|tx| {
            tx.run_contract_call(
                &boot_code_addr(false).into(),
                None,
                POX_2_CONTRACT_TESTNET.deref(),
                "set-burnchain-parameters",
                &[
                    Value::UInt(0),
                    Value::UInt(30),
                    Value::UInt(150),
                    Value::UInt(25),
                    Value::UInt(0),
                ],
                |_, _| false,
            )
        })
        .unwrap();
    });

    sim.execute_next_block(|env| {
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(2 * USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "Successfully setup delegate relationship between User0 and delegate",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(2 * USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "Successfully setup delegate relationship between User1 and delegate",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[1]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(10)
                ])
            )
            .unwrap()
            .0.to_string(),
            "(err 26)".to_string(),
            "Should not be able to delegate-stack-extend before locking",
        );

        let burn_height = env.eval_raw("burn-block-height").unwrap().0;
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[0]),
                Value::UInt(*MIN_THRESHOLD - 1),
                Value::UInt(450)
            )),
            "Delegate should successfully stack through delegation from User0",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[1]).into(),
                    Value::UInt(1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[1]),
                Value::UInt(1),
                Value::UInt(450)
            )),
            "Delegate should successfully stack through delegation from User1",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(1)])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string(),
            "Delegate should successfully aggregate commits for cycle 1",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(2)])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string(),
            "Delegate should successfully aggregate commits for cycle 2",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(3)])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 4)".to_string(),
            "Delegate does not have enough aggregate locked up for cycle 3",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[1]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(11)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 2)",
            "Delegate should not be able to extend over 12 cycles into future (current cycle is 0, previously stacked to 2, extend by 11 disallowed)",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[1]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(10)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[1]),
                // unlock-burn-height should be 10 reward cycles greater than prior unlock height
                Value::UInt(450 + 10 * 150),
            )),
            "Delegate should be able to extend 12 cycles into future (current cycle is 0, previously stacked to 2, extend by 10 allowed).",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(3)])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 11)".to_string(),
            "Delegate still does not have enough aggregate locked up for cycle 3",
        );


        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "revoke-delegate-stx",
                &[]
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "User0 successfully revokes delegation relationship",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(10)
                ])
            )
            .unwrap()
            .0.to_string(),
            "(err 9)".to_string(),
            "Delegate cannot stack-extend for User0 after revocation",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(1),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "User0 successfully re-inits delegation relationship with a `amount-ustx` = 1",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(10)
                ])
            )
            .unwrap()
            .0.to_string(),
            "(err 22)".to_string(),
            "Delegate cannot stack-extend for User0 because it would require more than User0's allowed amount (1)",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "revoke-delegate-stx",
                &[]
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "User0 successfully revokes delegation relationship",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(10_000_000),
                    (&delegator).into(),
                    Value::none(),
                    Value::some(POX_ADDRS[2].clone()).unwrap(),
                ])
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "User0 successfully re-inits delegation relationship with a `pox-addr` = POX_ADDR[2]",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(10)
                ])
            )
            .unwrap()
            .0.to_string(), "(err 23)".to_string(),
            "Delegate cannot stack-extend for User0 at POX_ADDR[1] because User0 specified to use POX_ADDR[2]",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "revoke-delegate-stx",
                &[]
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "User0 successfully revokes delegation relationship",
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(10_000_000),
                    (&delegator).into(),
                    Value::some(Value::UInt(450 + 10 * 150 - 1)).unwrap(),
                    Value::some(POX_ADDRS[1].clone()).unwrap(),
                ])
            )
            .unwrap()
            .0,
            Value::okay_true(),
            "User0 successfully re-inits delegation relationship with a `until-ht` one less than necessary for an extend-by-10",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(10)
                ])
            )
            .unwrap()
            .0.to_string(), "(err 21)".to_string(),
            "Delegate cannot stack-extend for User0 for 10 cycles",
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "delegate-stack-extend",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    POX_ADDRS[1].clone(),
                    Value::UInt(9)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[0]),
                // unlock-burn-height should be 9 reward cycles greater than prior unlock height
                Value::UInt(450 + 9 * 150),
            )),
            "Delegate successfully stack extends for User0 for 9 cycles",
        );

        for cycle in 3..12 {
            assert_eq!(
                env.execute_transaction(
                    (&delegator).into(),
                    None,
                    POX_2_CONTRACT_TESTNET.clone(),
                    "stack-aggregation-commit",
                    &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(cycle)])
                )
                    .unwrap()
                    .0
                    .to_string(),
                "(ok true)".to_string(),
                "For cycles in [3, 12), delegate has enough to successfully aggregate commit",
            );

            // call a second time to make sure that the partial map reset.
            assert_eq!(
                env.execute_transaction(
                    (&delegator).into(),
                    None,
                    POX_2_CONTRACT_TESTNET.clone(),
                    "stack-aggregation-commit",
                    &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(cycle)])
                )
                    .unwrap()
                    .0
                    .to_string(),
                "(err 4)".to_string(),
                "Delegate cannot aggregate commit a second time",
            );

        }

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_2_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(12)])
            )
                .unwrap()
                .0
                .to_string(),
            "(err 11)".to_string(),
            "At cycle 12, delegate cannot aggregate commit because only one stacker was extended by 10"
        );

        // check reward cycles [0, 20) for coherence
        // for cycles [1, 11] ==> delegate successfully committed the minimum threshold and should appear in the reward set
        // for all other cycles, reward set should be empty
        for cycle in 0..20 {
            eprintln!("Cycle number = {}, MIN_THRESHOLD  = {}", cycle, MIN_THRESHOLD.deref());
            let empty_set = cycle < 1 || cycle >= 12;
            let expected = if empty_set {
                "(u0 u0)".into()
            } else {
                format!("(u{} u1)", MIN_THRESHOLD.deref())
            };
            assert_eq!(
                env.eval_read_only(
                    &POX_2_CONTRACT_TESTNET,
                    &format!("(list (default-to u0 (get total-ustx (map-get? reward-cycle-total-stacked {{ reward-cycle: u{} }})))
                                    (default-to u0 (get len (map-get? reward-cycle-pox-address-list-len {{ reward-cycle: u{} }}))))",
                             cycle, cycle))
                    .unwrap()
                    .0
                    .to_string(),
                expected
            );
            if !empty_set {
                let expected_pox_addr = &POX_ADDRS[1];

                assert_eq!(
                    env.eval_read_only(
                        &POX_2_CONTRACT_TESTNET,
                        &format!("(unwrap-panic (map-get? reward-cycle-pox-address-list {{ reward-cycle: u{}, index: u0 }}))",
                                 cycle))
                        .unwrap()
                        .0,
                    execute(&format!(
                        "{{ pox-addr: {}, total-ustx: u{}, stacker: none }}",
                        expected_pox_addr,
                        MIN_THRESHOLD.deref(),
                    ))
                );
            }
        }
    });
}

#[test]
fn simple_epoch21_test() {
    let mut sim = ClarityTestSim::new();
    sim.epoch_bounds = vec![0, 1, 3];
    let delegator = StacksPrivateKey::new();

    let clarity_2_0_id =
        QualifiedContractIdentifier::new(StandardPrincipalData::transient(), "contract-2-0".into());
    let clarity_2_0_bad_id = QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        "contract-2-0-bad".into(),
    );
    let clarity_2_0_content = "
(define-private (stx-account (a principal)) 1)
(define-public (call-through)
  (ok (stx-account 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)))
";

    let clarity_2_1_id =
        QualifiedContractIdentifier::new(StandardPrincipalData::transient(), "contract-2-1".into());
    let clarity_2_1_bad_id = QualifiedContractIdentifier::new(
        StandardPrincipalData::transient(),
        "contract-2-1-bad".into(),
    );
    let clarity_2_1_content = "
(define-public (call-through)
  (let ((balance-1 (stx-account 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF))
        (balance-2 (unwrap-panic (contract-call? .contract-2-0 call-through)))
        (balance-3 (stx-account 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)))
       (print balance-1)
       (print balance-2)
       (print balance-3)
       (ok 1)))
(call-through)
";

    sim.execute_next_block_as_conn(|block| {
        test_deploy_smart_contract(
            block,
            &clarity_2_0_id,
            clarity_2_0_content,
            ClarityVersion::Clarity1,
        )
        .expect("2.0 'good' contract should deploy successfully");
        match test_deploy_smart_contract(
            block,
            &clarity_2_0_bad_id,
            clarity_2_1_content,
            ClarityVersion::Clarity1,
        )
        .expect_err("2.0 'bad' contract should not deploy successfully")
        {
            ClarityError::Analysis(e) => {
                assert_eq!(e.err, CheckErrors::UnknownFunction("stx-account".into()));
            }
            e => panic!("Should have caused an analysis error: {:#?}", e),
        };
    });
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});

    sim.execute_next_block_as_conn(|block| {
        test_deploy_smart_contract(
            block,
            &clarity_2_1_id,
            clarity_2_1_content,
            ClarityVersion::Clarity2,
        )
        .expect("2.1 'good' contract should deploy successfully");
        match test_deploy_smart_contract(
            block,
            &clarity_2_1_bad_id,
            clarity_2_0_content,
            ClarityVersion::Clarity2,
        )
        .expect_err("2.1 'bad' contract should not deploy successfully")
        {
            ClarityError::Interpreter(e) => {
                assert_eq!(
                    e,
                    Error::Unchecked(CheckErrors::NameAlreadyUsed("stx-account".into()))
                );
            }
            e => panic!("Should have caused an Interpreter error: {:#?}", e),
        };
    });
    sim.execute_next_block(|_env| {});
    sim.execute_next_block(|_env| {});
}

fn test_deploy_smart_contract(
    block: &mut ClarityBlockConnection,
    contract_id: &QualifiedContractIdentifier,
    content: &str,
    version: ClarityVersion,
) -> std::result::Result<(), ClarityError> {
    block.as_transaction(|tx| {
        let (mut ast, analysis) =
            tx.analyze_smart_contract(&contract_id, version, content, ASTRules::PrecheckSize)?;
        tx.initialize_smart_contract(
            &contract_id,
            version,
            &mut ast,
            &analysis,
            content,
            None,
            |_, _| false,
        )?;
        tx.save_analysis(&contract_id, &analysis)?;
        return Ok(());
    })
}

#[test]
// test that the maximum stackerdb list size will fit in a value
fn max_stackerdb_list() {
    let signers_list: Vec<_> = (0..SIGNERS_MAX_LIST_SIZE)
        .map(|signer_ix| {
            let signer_address = StacksAddress {
                version: 0,
                bytes: Hash160::from_data(&signer_ix.to_be_bytes()),
            };
            Value::Tuple(
                TupleData::from_data(vec![
                    (
                        "signer".into(),
                        Value::Principal(PrincipalData::from(signer_address)),
                    ),
                    ("num-slots".into(), Value::UInt(1)),
                ])
                .expect("BUG: Failed to construct `{ signer: principal, num-slots: u64 }` tuple"),
            )
        })
        .collect();

    assert_eq!(signers_list.len(), SIGNERS_MAX_LIST_SIZE);
    Value::cons_list_unsanitized(signers_list)
        .expect("Failed to construct `(list 4000 { signer: principal, num-slots: u64 })` list");
}

#[test]
fn recency_tests() {
    let mut sim = ClarityTestSim::new();
    let delegator = StacksPrivateKey::new();

    sim.execute_next_block(|env| {
        env.initialize_versioned_contract(
            POX_CONTRACT_TESTNET.clone(),
            ClarityVersion::Clarity2,
            &BOOT_CODE_POX_TESTNET,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap()
    });
    sim.execute_next_block(|env| {
        // try to issue a far future stacking tx
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "stack-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[0].clone(),
                    Value::UInt(3000),
                    Value::UInt(3),
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 24)".to_string()
        );
        // let's delegate, and check if the delegate can issue a far future
        //   stacking tx
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(2 * USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true()
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(USTX_PER_HOLDER),
                    POX_ADDRS[1].clone(),
                    Value::UInt(3000),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 24)".to_string()
        );
    });
}

#[test]
fn delegation_tests() {
    let mut sim = ClarityTestSim::new();
    let delegator = StacksPrivateKey::new();
    const REWARD_CYCLE_LENGTH: u128 = 1050;

    sim.execute_next_block(|env| {
        env.initialize_versioned_contract(
            POX_CONTRACT_TESTNET.clone(),
            ClarityVersion::Clarity2,
            &BOOT_CODE_POX_TESTNET,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap()
    });
    sim.execute_next_block(|env| {
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(2 * USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true()
        );

        // already delegating...
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::error(Value::Int(20)).unwrap()
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[1]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::some(POX_ADDRS[0].clone()).unwrap()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true()
        );
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[2]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::some(Value::UInt(REWARD_CYCLE_LENGTH * 2)).unwrap(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true()
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[3]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true()
        );

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[4]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stx",
                &symbols_from_values(vec![
                    Value::UInt(USTX_PER_HOLDER),
                    (&delegator).into(),
                    Value::none(),
                    Value::none()
                ])
            )
            .unwrap()
            .0,
            Value::okay_true()
        );
    });
    // let's do some delegated stacking!
    sim.execute_next_block(|env| {
        // try to stack more than [0]'s delegated amount!
        let burn_height = env.eval_raw("burn-block-height").unwrap().0;
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(3 * USTX_PER_HOLDER),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 22)".to_string()
        );

        // try to stack more than [0] has!
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(2 * USTX_PER_HOLDER),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 1)".to_string()
        );

        // let's stack less than the threshold
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[0]),
                Value::UInt(*MIN_THRESHOLD - 1),
                Value::UInt(REWARD_CYCLE_LENGTH * 3)
            ))
        );

        assert_eq!(
            env.eval_read_only(
                &POX_CONTRACT_TESTNET,
                &format!("(stx-get-balance '{})", &Value::from(&USER_KEYS[0]))
            )
            .unwrap()
            .0,
            Value::UInt(USTX_PER_HOLDER - *MIN_THRESHOLD + 1)
        );

        // try to commit our partial stacking...
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(1)])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 11)".to_string()
        );
        // not enough! we need to stack more...
        //   but POX_ADDR[1] cannot be used for USER_KEYS[1]...
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[1]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 23)".to_string()
        );

        // And USER_KEYS[0] is already stacking...
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[0]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 3)".to_string()
        );

        // USER_KEYS[2] won't want to stack past the delegation expiration...
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[2]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 21)".to_string()
        );

        //  but for just one block will be fine
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[2]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(1)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[2]),
                Value::UInt(*MIN_THRESHOLD - 1),
                Value::UInt(REWARD_CYCLE_LENGTH * 2)
            ))
        );

        assert_eq!(
            env.eval_read_only(
                &POX_CONTRACT_TESTNET,
                &format!("(stx-get-balance '{})", &Value::from(&USER_KEYS[2]))
            )
            .unwrap()
            .0,
            Value::UInt(USTX_PER_HOLDER - *MIN_THRESHOLD + 1)
        );

        assert_eq!(
            env.eval_read_only(
                &POX_CONTRACT_TESTNET,
                &format!("(stx-get-balance '{})", &Value::from(&USER_KEYS[0]))
            )
            .unwrap()
            .0,
            Value::UInt(USTX_PER_HOLDER - *MIN_THRESHOLD + 1)
        );

        assert_eq!(
            env.eval_read_only(
                &POX_CONTRACT_TESTNET,
                &format!("(stx-get-balance '{})", &Value::from(&USER_KEYS[1]))
            )
            .unwrap()
            .0,
            Value::UInt(USTX_PER_HOLDER)
        );

        // try to commit our partial stacking again!
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(1)])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string()
        );

        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-size u1)")
                .unwrap()
                .0
                .to_string(),
            "u1"
        );
        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-pox-address u1 u0)")
                .unwrap()
                .0,
            execute(&format!(
                "(some {{ pox-addr: {}, total-ustx: {} }})",
                &POX_ADDRS[1],
                &Value::UInt(2 * (*MIN_THRESHOLD - 1))
            ))
        );

        // can we double commit? I don't think so!
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(1)])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 4)".to_string()
        );

        // okay, let's try some more delegation situations...
        // 1. we already locked user[0] up for round 2, so let's add some more stacks for round 2 from
        //    user[3]. in the process, this will add more stacks for lockup in round 1, so lets commit
        //    that as well.

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[3]).into(),
                    Value::UInt(*MIN_THRESHOLD),
                    POX_ADDRS[1].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[3]),
                Value::UInt(*MIN_THRESHOLD),
                Value::UInt(REWARD_CYCLE_LENGTH * 3)
            ))
        );

        assert_eq!(
            env.eval_read_only(
                &POX_CONTRACT_TESTNET,
                &format!("(stx-get-balance '{})", &Value::from(&USER_KEYS[3]))
            )
            .unwrap()
            .0,
            Value::UInt(USTX_PER_HOLDER - *MIN_THRESHOLD)
        );

        // let's commit to round 2 now.
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(2)])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string()
        );

        // and we can commit to round 1 again as well!
        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "stack-aggregation-commit",
                &symbols_from_values(vec![POX_ADDRS[1].clone(), Value::UInt(1)])
            )
            .unwrap()
            .0
            .to_string(),
            "(ok true)".to_string()
        );

        // check reward sets for round 2 and round 1...

        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-size u2)")
                .unwrap()
                .0
                .to_string(),
            "u1"
        );
        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-pox-address u2 u0)")
                .unwrap()
                .0,
            execute(&format!(
                "(some {{ pox-addr: {}, total-ustx: {} }})",
                &POX_ADDRS[1],
                &Value::UInt(2 * (*MIN_THRESHOLD) - 1)
            ))
        );

        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-size u1)")
                .unwrap()
                .0
                .to_string(),
            "u2"
        );
        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-pox-address u1 u0)")
                .unwrap()
                .0,
            execute(&format!(
                "(some {{ pox-addr: {}, total-ustx: {} }})",
                &POX_ADDRS[1],
                &Value::UInt(2 * (*MIN_THRESHOLD - 1))
            ))
        );
        assert_eq!(
            env.eval_read_only(&POX_CONTRACT_TESTNET, "(get-reward-set-pox-address u1 u1)")
                .unwrap()
                .0,
            execute(&format!(
                "(some {{ pox-addr: {}, total-ustx: {} }})",
                &POX_ADDRS[1],
                &Value::UInt(*MIN_THRESHOLD)
            ))
        );

        // 2. lets make sure we can lock up for user[1] so long as it goes to pox[0].

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[1]).into(),
                    Value::UInt(*MIN_THRESHOLD),
                    POX_ADDRS[0].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0,
            execute(&format!(
                "(ok {{ stacker: '{}, lock-amount: {}, unlock-burn-height: {} }})",
                Value::from(&USER_KEYS[1]),
                Value::UInt(*MIN_THRESHOLD),
                Value::UInt(REWARD_CYCLE_LENGTH * 3)
            ))
        );

        // 3. lets try to lock up user[4], but do some revocation first.
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[4]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "revoke-delegate-stx",
                &[]
            )
            .unwrap()
            .0,
            Value::okay_true()
        );

        // will run a second time, but return false
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[4]).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "revoke-delegate-stx",
                &[]
            )
            .unwrap()
            .0
            .to_string(),
            "(ok false)".to_string()
        );

        assert_eq!(
            env.execute_transaction(
                (&delegator).into(),
                None,
                POX_CONTRACT_TESTNET.clone(),
                "delegate-stack-stx",
                &symbols_from_values(vec![
                    (&USER_KEYS[4]).into(),
                    Value::UInt(*MIN_THRESHOLD - 1),
                    POX_ADDRS[0].clone(),
                    burn_height.clone(),
                    Value::UInt(2)
                ])
            )
            .unwrap()
            .0
            .to_string(),
            "(err 9)".to_string()
        );
    });
}

#[test]
fn test_vote_withdrawal() {
    let mut sim = ClarityTestSim::new();

    sim.execute_next_block(|env| {
        env.initialize_versioned_contract(
            COST_VOTING_CONTRACT_TESTNET.clone(),
            ClarityVersion::Clarity1,
            &BOOT_CODE_COST_VOTING,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

        // Submit a proposal
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "submit-proposal",
                &symbols_from_values(vec![
                    Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST000000000000000000002AMW42H.function-name"
                        )
                        .unwrap()
                    ),
                    Value::string_ascii_from_bytes("function-name".into()).unwrap(),
                    Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST000000000000000000002AMW42H.cost-function-name"
                        )
                        .unwrap()
                    ),
                    Value::string_ascii_from_bytes("cost-function-name".into()).unwrap(),
                ])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::UInt(0).into()
            })
        );

        // Vote on the proposal
        env.execute_transaction(
            (&USER_KEYS[0]).into(),
            None,
            COST_VOTING_CONTRACT_TESTNET.clone(),
            "vote-proposal",
            &symbols_from_values(vec![Value::UInt(0), Value::UInt(10)]),
        )
        .unwrap();

        // Assert that the number of votes is correct
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "get-proposal-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Optional(OptionalData {
                data: Some(Box::from(Value::UInt(10)))
            })
        );

        // Vote again on the proposal
        env.execute_transaction(
            (&USER_KEYS[0]).into(),
            None,
            COST_VOTING_CONTRACT_TESTNET.clone(),
            "vote-proposal",
            &symbols_from_values(vec![Value::UInt(0), Value::UInt(5)]),
        )
        .unwrap();

        // Assert that the number of votes is correct
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "get-proposal-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Optional(OptionalData {
                data: Some(Box::from(Value::UInt(15)))
            })
        );

        // Assert votes are assigned to principal
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "get-principal-votes",
                &symbols_from_values(vec![
                    Value::Principal(StandardPrincipalData::from(&USER_KEYS[0]).into()),
                    Value::UInt(0),
                ])
            )
            .unwrap()
            .0,
            Value::Optional(OptionalData {
                data: Some(Box::from(Value::UInt(15)))
            })
        );

        // Assert withdrawal fails if amount is more than voted
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "withdraw-votes",
                &symbols_from_values(vec![Value::UInt(0), Value::UInt(20)]),
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: false,
                data: Value::Int(5).into()
            })
        );

        // Withdraw votes
        env.execute_transaction(
            (&USER_KEYS[0]).into(),
            None,
            COST_VOTING_CONTRACT_TESTNET.clone(),
            "withdraw-votes",
            &symbols_from_values(vec![Value::UInt(0), Value::UInt(5)]),
        )
        .unwrap();

        // Assert withdrawal worked
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "get-proposal-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Optional(OptionalData {
                data: Some(Box::from(Value::UInt(10)))
            })
        );
    });

    // Fast forward to proposal expiration
    for _ in 0..2016 {
        sim.execute_next_block(|_| {});
    }

    sim.execute_next_block(|env| {
        // Withdraw STX after proposal expires
        env.execute_transaction(
            (&USER_KEYS[0]).into(),
            None,
            COST_VOTING_CONTRACT_TESTNET.clone(),
            "withdraw-votes",
            &symbols_from_values(vec![Value::UInt(0), Value::UInt(10)]),
        )
        .unwrap();
    });

    sim.execute_next_block(|env| {
        // Assert that stx balance is correct
        assert_eq!(
            env.eval_read_only(
                &COST_VOTING_CONTRACT_TESTNET,
                &format!("(stx-get-balance '{})", &Value::from(&USER_KEYS[0]))
            )
            .unwrap()
            .0,
            Value::UInt(1000000)
        );
    });
}

#[test]
fn test_vote_fail() {
    let mut sim = ClarityTestSim::new();

    // Test voting in a proposal
    sim.execute_next_block(|env| {
        env.initialize_contract(
            COST_VOTING_CONTRACT_TESTNET.clone(),
            &BOOT_CODE_COST_VOTING,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

        // Submit a proposal
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "submit-proposal",
                &symbols_from_values(vec![
                    Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST000000000000000000002AMW42H.function-name2"
                        )
                        .unwrap()
                    ),
                    Value::string_ascii_from_bytes("function-name2".into()).unwrap(),
                    Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST000000000000000000002AMW42H.cost-function-name2"
                        )
                        .unwrap()
                    ),
                    Value::string_ascii_from_bytes("cost-function-name2".into()).unwrap(),
                ])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::UInt(0).into()
            })
        );

        // Assert confirmation fails
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: false,
                data: Value::Int(11).into()
            })
        );

        // Assert voting with more STX than are in an account fails
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "vote-proposal",
                &symbols_from_values(vec![Value::UInt(0), Value::UInt(USTX_PER_HOLDER + 1)]),
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: false,
                data: Value::Int(5).into()
            })
        );

        // Commit all liquid stacks to vote
        for user in USER_KEYS.iter() {
            env.execute_transaction(
                user.into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "vote-proposal",
                &symbols_from_values(vec![Value::UInt(0), Value::UInt(USTX_PER_HOLDER)]),
            )
            .unwrap();
        }

        // Assert confirmation returns true
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::Bool(true).into()
            })
        );
    });

    sim.execute_next_block(|env| {
        env.execute_transaction(
            (&MINER_KEY.clone()).into(),
            None,
            COST_VOTING_CONTRACT_TESTNET.clone(),
            "veto",
            &symbols_from_values(vec![Value::UInt(0)]),
        )
        .unwrap();

        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "get-proposal-vetos",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Optional(OptionalData {
                data: Some(Box::from(Value::UInt(1)))
            })
        );
    });

    let fork_start = sim.block_height;

    for i in 0..25 {
        sim.execute_next_block(|env| {
            env.execute_transaction(
                (&MINER_KEY.clone()).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "veto",
                &symbols_from_values(vec![Value::UInt(0)]),
            )
            .unwrap();

            // assert error if already vetoed in this block
            assert_eq!(
                env.execute_transaction(
                    (&MINER_KEY.clone()).into(),
                    None,
                    COST_VOTING_CONTRACT_TESTNET.clone(),
                    "veto",
                    &symbols_from_values(vec![Value::UInt(0)])
                )
                .unwrap()
                .0,
                Value::Response(ResponseData {
                    committed: false,
                    data: Value::Int(9).into()
                })
            );
        })
    }

    for _ in 0..100 {
        sim.execute_next_block(|_| {});
    }

    sim.execute_next_block(|env| {
        // Assert confirmation fails because of majority veto
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-miners",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: false,
                data: Value::Int(14).into()
            })
        );
    });

    // let's fork, and overcome the veto
    sim.execute_block_as_fork(fork_start, |_| {});
    for _ in 0..125 {
        sim.execute_next_block(|_| {});
    }

    sim.execute_next_block(|env| {
        // Assert confirmation passes because there are no vetos
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-miners",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::Bool(true).into(),
            })
        );
    });
}

#[test]
fn test_vote_confirm() {
    let mut sim = ClarityTestSim::new();

    sim.execute_next_block(|env| {
        env.initialize_contract(
            COST_VOTING_CONTRACT_TESTNET.clone(),
            &BOOT_CODE_COST_VOTING,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

        // Submit a proposal
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "submit-proposal",
                &symbols_from_values(vec![
                    Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST000000000000000000002AMW42H.function-name2"
                        )
                        .unwrap()
                    ),
                    Value::string_ascii_from_bytes("function-name2".into()).unwrap(),
                    Value::Principal(
                        PrincipalData::parse_qualified_contract_principal(
                            "ST000000000000000000002AMW42H.cost-function-name2"
                        )
                        .unwrap()
                    ),
                    Value::string_ascii_from_bytes("cost-function-name2".into()).unwrap(),
                ])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::UInt(0).into()
            })
        );

        // Assert confirmation fails
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: false,
                data: Value::Int(11).into()
            })
        );

        // Commit all liquid stacks to vote
        for user in USER_KEYS.iter() {
            env.execute_transaction(
                user.into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "vote-proposal",
                &symbols_from_values(vec![Value::UInt(0), Value::UInt(USTX_PER_HOLDER)]),
            )
            .unwrap();
        }

        // Assert confirmation returns true
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-votes",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::Bool(true).into()
            })
        );
    });

    // Fast forward to proposal expiration
    for _ in 0..2016 {
        sim.execute_next_block(|_| {});
    }

    for _ in 0..1007 {
        sim.execute_next_block(|_| {});
    }

    sim.execute_next_block(|env| {
        // Assert confirmation passes
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-miners",
                &symbols_from_values(vec![Value::UInt(0)])
            )
            .unwrap()
            .0,
            Value::Response(ResponseData {
                committed: true,
                data: Value::Bool(true).into()
            })
        );
    });
}

#[test]
fn test_vote_too_many_confirms() {
    let mut sim = ClarityTestSim::new();

    let MAX_CONFIRMATIONS_PER_BLOCK = 10;
    sim.execute_next_block(|env| {
        env.initialize_contract(
            COST_VOTING_CONTRACT_TESTNET.clone(),
            &BOOT_CODE_COST_VOTING,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

        // Submit a proposal
        for i in 0..(MAX_CONFIRMATIONS_PER_BLOCK + 1) {
            assert_eq!(
                env.execute_transaction(
                    (&USER_KEYS[0]).into(),
                    None,
                    COST_VOTING_CONTRACT_TESTNET.clone(),
                    "submit-proposal",
                    &symbols_from_values(vec![
                        Value::Principal(
                            PrincipalData::parse_qualified_contract_principal(
                                "ST000000000000000000002AMW42H.function-name2"
                            )
                            .unwrap()
                        ),
                        Value::string_ascii_from_bytes("function-name2".into()).unwrap(),
                        Value::Principal(
                            PrincipalData::parse_qualified_contract_principal(
                                "ST000000000000000000002AMW42H.cost-function-name2"
                            )
                            .unwrap()
                        ),
                        Value::string_ascii_from_bytes("cost-function-name2".into()).unwrap(),
                    ])
                )
                .unwrap()
                .0,
                Value::Response(ResponseData {
                    committed: true,
                    data: Value::UInt(i).into()
                })
            );
        }

        for i in 0..(MAX_CONFIRMATIONS_PER_BLOCK + 1) {
            // Commit all liquid stacks to vote
            for user in USER_KEYS.iter() {
                assert_eq!(
                    env.execute_transaction(
                        user.into(),
                        None,
                        COST_VOTING_CONTRACT_TESTNET.clone(),
                        "vote-proposal",
                        &symbols_from_values(vec![Value::UInt(i), Value::UInt(USTX_PER_HOLDER)]),
                    )
                    .unwrap()
                    .0,
                    Value::okay_true()
                );
            }

            // Assert confirmation returns true
            assert_eq!(
                env.execute_transaction(
                    (&USER_KEYS[0]).into(),
                    None,
                    COST_VOTING_CONTRACT_TESTNET.clone(),
                    "confirm-votes",
                    &symbols_from_values(vec![Value::UInt(i)])
                )
                .unwrap()
                .0,
                Value::okay_true(),
            );

            // withdraw
            for user in USER_KEYS.iter() {
                env.execute_transaction(
                    user.into(),
                    None,
                    COST_VOTING_CONTRACT_TESTNET.clone(),
                    "withdraw-votes",
                    &symbols_from_values(vec![Value::UInt(i), Value::UInt(USTX_PER_HOLDER)]),
                )
                .unwrap();
            }
        }
    });

    // Fast forward to proposal expiration
    for _ in 0..2016 {
        sim.execute_next_block(|_| {});
    }

    for _ in 0..1007 {
        sim.execute_next_block(|_| {});
    }

    sim.execute_next_block(|env| {
        for i in 0..MAX_CONFIRMATIONS_PER_BLOCK {
            // Assert confirmation passes
            assert_eq!(
                env.execute_transaction(
                    (&USER_KEYS[0]).into(),
                    None,
                    COST_VOTING_CONTRACT_TESTNET.clone(),
                    "confirm-miners",
                    &symbols_from_values(vec![Value::UInt(i)])
                )
                .unwrap()
                .0,
                Value::okay_true(),
            );
        }

        // Assert next confirmation fails
        assert_eq!(
            env.execute_transaction(
                (&USER_KEYS[0]).into(),
                None,
                COST_VOTING_CONTRACT_TESTNET.clone(),
                "confirm-miners",
                &symbols_from_values(vec![Value::UInt(MAX_CONFIRMATIONS_PER_BLOCK)])
            )
            .unwrap()
            .0,
            Value::error(Value::Int(17)).unwrap()
        );
    });
}
