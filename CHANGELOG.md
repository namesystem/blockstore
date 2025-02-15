# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the versioning scheme outlined in the [README.md](README.md).

## [Unreleased]

## Added

- The `BlockProposal` StackerDB message serialization struct now includes a `server_version` string, which represents the version of the node that the miner is using. ([#5803](https://github.com/stacks-network/stacks-core/pull/5803))
- Add `vrf_seed` to the `/v3/sortitions` rpc endpoint

### Changed

- Miner will stop waiting for signatures on a block if the Stacks tip advances (causing the block it had proposed to be invalid).
- Logging improvements:
  - P2P logs now includes a reason for dropping a peer or neighbor
  - Improvements to how a PeerAddress is logged (human readable format vs hex)
  - Add weight threshold and percentages to `StackerDBListener` logs

### Fixed

- Error responses to /v2/transactions/fees are once again expressed as JSON ([#4145](https://github.com/stacks-network/stacks-core/issues/4145)).

## [3.1.0.0.5]

### Added

- Add miner configuration option `tenure_extend_cost_threshold` to specify the percentage of the tenure budget that must be spent before a time-based tenure extend is attempted
- Add miner configuration option `tenure_extend_wait_timeout_ms` to specify the time to wait before trying to continue a tenure because the next miner did not produce blocks

### Changed

- Miner will include other transactions in blocks with tenure extend transactions (#5760)
- Add `block_rejection_timeout_steps` to miner configuration for defining rejections-based timeouts while waiting for signers response (#5705)
- Miner will not issue a tenure extend until at least half of the block budget has been spent (#5757)
- Miner will issue a tenure extend if the incoming miner has failed to produce a block (#5729)

### Fixed

- Miners who restart their nodes immediately before a winning tenure now correctly detect that
  they won the tenure after their nodes restart ([#5750](https://github.com/stacks-network/stacks-core/issues/5750)).

## [3.1.0.0.4]

### Added

- The stacks-node miner now performs accurate tenure-extensions in certain bitcoin block production
  cases: when a bitcoin block is produced before the previous bitcoin block's Stacks tenure started.
  Previously, the miner had difficulty restarting their missed tenure and extending into the new
  bitcoin block, leading to 1-2 bitcoin blocks of missed Stacks block production.
- The event dispatcher now includes `consensus_hash` in the `/new_block` and `/new_burn_block` payloads. ([#5677](https://github.com/stacks-network/stacks-core/pull/5677))

## Changed

- When a miner reorgs the previous tenure due to a poorly timed block, it can now continue to build blocks on this new chain tip (#5691)

## [3.1.0.0.3]

### Added

- Add `tenure_timeout_secs` to the miner for determining when a time-based tenure extend should be attempted.
- Added configuration option `block_proposal_max_age_secs` under `[connection_options]` to prevent processing stale block proposals

### Changed

- The RPC endpoint `/v3/block_proposal` no longer will evaluate block proposals more than `block_proposal_max_age_secs` old
- When a transaction is dropped due to replace-by-fee, the `/drop_mempool_tx` event observer payload now includes `new_txid`, which is the transaction that replaced this dropped transaction. When a transaction is dropped for other reasons, `new_txid` is `null`. [#5381](https://github.com/stacks-network/stacks-core/pull/5381)
- Nodes will assume that all PoX anchor blocks exist by default, and stall initial block download indefinitely to await their arrival (#5502)

### Fixed

- Signers no longer accept messages for blocks from different reward cycles (#5662)

## [3.1.0.0.2]

### Added

- **SIP-029 consensus rules, activating in epoch 3.1 at block 875,000** (see [SIP-029](https://github.com/stacksgov/sips/blob/main/sips/sip-029/sip-029-halving-alignment.md) for details)
- New RPC endpoints
  - `/v2/clarity/marf/:marf_key_hash`
  - `/v2/clarity/metadata/:principal/:contract_name/:clarity_metadata_key`
- When a proposed block is validated by a node, the block can be validated even when the block version is different than the node's default ([#5539](https://github.com/stacks-network/stacks-core/pull/5539))
- A miner will now generate a tenure-extend when at least 70% of the signers have confirmed that they are willing to allow one, via the new timestamp included in block responses. This allows the miner to refresh its budget in between Bitcoin blocks. ([#5476](https://github.com/stacks-network/stacks-core/discussions/5476))
- Set the epoch to 3.1 in the Clarity DB upon activation.

### Changed

## [3.0.0.0.4]

### Added

### Changed

- Use the same burn view loader in both block validation and block processing

## [3.0.0.0.3]

### Added

### Changed
- Add index for StacksBlockId to nakamoto block headers table (improves node performance)
- Remove the panic for reporting DB deadlocks (just error and continue waiting)
- Add index to `metadata_table` in Clarity DB on `blockhash`
- Add `block_commit_delay_ms` to the config file to control the time to wait after seeing a new burn block, before submitting a block commit, to allow time for the first Nakamoto block of the new tenure to be mined, allowing this miner to avoid the need to RBF the block commit.
- Add `tenure_cost_limit_per_block_percentage` to the miner config file to control the percentage remaining tenure cost limit to consume per nakamoto block.
- Add `/v3/blocks/height/:block_height` rpc endpoint
- If the winning miner of a sortition is committed to the wrong parent tenure, the previous miner can immediately tenure extend and continue mining since the winning miner would never be able to propose a valid block. (#5361)

## [3.0.0.0.2]

### Added

### Changed
- Fixes  a few bugs in the relayer and networking stack
  - detects and deprioritizes unhealthy replicas
  - fixes an issue in the p2p stack which was preventing it from caching the reward set.

## [3.0.0.0.1]

### Changed
- Add index for StacksBlockId to nakamoto block headers table (improves node performance)
- Remove the panic for reporting DB deadlocks (just error and continue waiting)
- Various test fixes for CI (5353, 5368, 5372, 5371, 5380, 5378, 5387, 5396, 5390, 5394)
- Various log fixes:
    - don't say proceeding to mine blocks if not a miner
    - misc. warns downgraded to debugs
- 5391: Update default block proposal timeout to 10 minutes
- 5406: After block rejection, miner pauses
- Docs fixes
    - Fix signer docs link
    - Specify burn block in clarity docs

## [3.0.0.0.0]

### Added

- **Nakamoto consensus rules, activating in epoch 3.0 at block 867,867** (see [SIP-021](https://github.com/stacksgov/sips/blob/main/sips/sip-021/sip-021-nakamoto.md) for details)
- Clarity 3, activating with epoch 3.0
  - Keywords / variable
    - `tenure-height` added
    - `stacks-block-height` added
    - `block-height` removed
  - Functions
    - `get-stacks-block-info?` added
    - `get-tenure-info?` added
    - `get-block-info?` removed
- New RPC endpoints
  - `/v3/blocks/:block_id`
  - `/v3/blocks/upload/`
  - `/v3/signer/:signer_pubkey/:cycle_num`
  - `/v3/sortitions`
  - `/v3/stacker_set/:cycle_num`
  - `/v3/tenures/:block_id`
  - `/v3/tenures/fork_info/:start/:stop`
  - `/v3/tenures/info`
  - `/v3/tenures/tip/:consensus_hash`
- Re-send events to event observers across restarts
- Support custom chain-ids for testing
- Add `replay-block` command to CLI

### Changed

- Strict config file validation (unknown fields will cause the node to fail to start)
- Add optional `timeout_ms` to `events_observer` configuration
- Modified RPC endpoints
  - Include `tenure_height` in `/v2/info` endpoint
  - Include `block_time` and `tenure_height` in `/new/block` event payload
- Various improvements to logging, reducing log spam and improving log messages
- Various improvements and bugfixes

## [2.5.0.0.7]

### Added

- Add warn logs for block validate rejections (#5079)
- Neon mock miner replay (#5060)

### Changed

- Revert BurnchainHeaderHash serialization change (#5094)
- boot_to_epoch_3 in SignerTest should wait for a new commit (#5087)
- Fix block proposal rejection test (#5084)
- Mock signing revamp (#5070)
- Multi miner fixes jude (#5040)
- Remove spurious deadlock condition whenever the sortition DB is opened

## [2.5.0.0.6]

### Changed

- If there is a getchunk/putchunk that fails due to a stale (or future) version NACK, the StackerDB sync state machine should immediately retry sync (#5066)

## [2.5.0.0.5]

### Added

- Added configuration option `connections.antientropy_retry` (#4932)

### Changed

- Set default antientropy_retry to run once per hour (#4935)

## [2.5.0.0.4]

### Added

- Adds the solo stacking scenarios to the stateful property-based testing strategy for PoX-4 (#4725)
- Add signer-key to synthetic stack-aggregation-increase event (#4728)
- Implement the assumed total commit with carry-over (ATC-C) strategy for denying opportunistic Bitcoin miners from mining Stacks at a discount (#4733)
- Adding support for stacks-block-height and tenure-height in Clarity 3 (#4745)
- Preserve PeerNetwork struct when transitioning to 3.0 (#4767)
- Implement singer monitor server error (#4773)
- Pull current stacks signer out into v1 implementation and create placeholder v0 mod (#4778)
- Create new block signature message type for v0 signer (#4787)
- Isolate the rusqlite dependency in stacks-common and clarity behind a cargo feature (#4791)
- Add next_initiative_delay config option to control how frequently the miner checks if a new burnchain block has been processed (#4795)
- Various performance improvements and cleanup

### Changed

- Downgraded log messages about transactions from warning to info (#4697)
- Fix race condition between the signer binary and the /v2/pox endpoint (#4738)
- Make node config mock_miner item hot-swappable (#4743)
- Mandates that a burnchain block header be resolved by a BurnchainHeaderReader, which will resolve a block height to at most one burnchain header (#4748)
- Optional config option to resolve DNS of bootstrap nodes (#4749)
- Limit inventory syncs with new peers (#4750)
- Update /v2/fees/transfer to report the median transaction fee estimate for a STX-transfer of 180 bytes (#4754)
- Reduce connection spamming in stackerdb (#4759)
- Remove deprecated signer cli commands (#4772)
- Extra pair of signer slots got introduced at the epoch 2.5 boundary (#4845, #4868, #4891)
- Never consider Stacks chain tips that are not on the canonical burn chain #4886 (#4893)

### Fixed

- Allow Nakamoto blocks to access the burn block associated with the current tenure (#4333)

## [2.5.0.0.3]

This release fixes a regression in `2.5.0.0.0` from `2.4.0.1.0` caused by git merge

## [2.5.0.0.2]

This release fixes two bugs in `2.5.0.0.0`, correctly setting the activation height for 2.5, and the network peer version.

## [2.5.0.0.0]

This release implements the 2.5 Stacks consensus rules which activates at Bitcoin block `840,360`: primarily the instantiation
of the pox-4 contract. For more details see SIP-021.

This is the first consensus-critical release for Nakamoto. Nodes which do not update before the 2.5 activation height will be forked away from the rest of the network. This release is compatible with 2.4.x chain state directories and does not require resyncing from genesis. The first time a node boots with this version it will perform some database migrations which could lengthen the normal node startup time.

**This is a required release before Nakamoto rules are enabled in 3.0.**

### Timing of Release from 2.5 to 3.0

Activating Nakamoto will include two epochs:

- **Epoch 2.5:** Pox-4 contract is booted up but no Nakamoto consensus rules take effect.
- **Epoch 3:** Nakamoto consensus rules take effect.

### Added

- New RPC endpoint `/v2/stacker_set/{cycle_number}` to fetch stacker sets in PoX-4
- New `/new_pox_anchor` endpoint for broadcasting PoX anchor block processing.
- Stacker bitvec in NakamotoBlock
- New [`pox-4` contract](./stackslib/src/chainstate/stacks/boot/pox-4.clar) that reflects changes in how Stackers are signers in Nakamoto:
  - `stack-stx`, `stack-extend`, `stack-increase` and `stack-aggregation-commit` now include a `signer-key` parameter, which represents the public key used by the Signer. This key is used for determining the signer set in Nakamoto.
  - Functions that include a `signer-key` parameter also include a `signer-sig` parameter to demonstrate that the owner of `signer-key` is approving that particular Stacking operation. For more details, refer to the `verify-signer-key-sig` method in the `pox-4` contract.
  - Signer key authorizations can be added via `set-signer-key-authorization` to omit the need for `signer-key` signatures
  - A `max-amount` field is a field in signer key authorizations and defines the maximum amount of STX that can be locked in a single transaction.
- Added configuration parameters to customize the burn block at which to start processing Stacks blocks, when running on testnet or regtest.
  ```
  [burnchain]
  first_burn_block_height = 2582526
  first_burn_block_timestamp = 1710780828
  first_burn_block_hash = "000000000000001a17c68d43cb577d62074b63a09805e4a07e829ee717507f66"
  ```

### Modified

- `pox-4.aggregation-commit` contains a signing-key parameter (like
  `stack-stx` and `stack-extend`), the signing-key parameter is removed from
  `delegate-*` functions.

## [2.4.0.1.0]

### Added

- When the Clarity library is built with feature flag `developer-mode`, comments
  from the source code are now attached to the `SymbolicExpression` nodes. This
  will be useful for tools that use the Clarity library to analyze and
  manipulate Clarity source code, e.g. a formatter.
- New RPC endpoint at /v2/constant_val to fetch a constant from a contract.
- A new subsystem, called StackerDB, has been added, which allows a set of
  Stacks nodes to store off-chain data on behalf of a specially-crafter smart
  contract. This is an opt-in feature; Stacks nodes explicitly subscribe to
  StackerDB replicas in their config files.
- Message definitions and codecs for Stacker DB, a replicated off-chain DB
  hosted by subscribed Stacks nodes and controlled by smart contracts
- Added 3 new public and regionally diverse bootstrap nodes: est.stacksnodes.org, cet.stacksnodes.org, sgt.stacksnodes.org
- satoshis_per_byte can be changed in the config file and miners will always use
  the most up to date value
- New RPC endpoint at /v2/block_proposal for miner to validate proposed block.
  Only accessible on local loopback interface

In addition, this introduces a set of improvements to the Stacks miner behavior. In
particular:

- The VRF public key can be re-used across node restarts.
- Settings that affect mining are hot-reloaded from the config file. They take
  effect once the file is updated; there is no longer a need to restart the
  node.
- The act of changing the miner settings in the config file automatically
  triggers a subsequent block-build attempt, allowing the operator to force the
  miner to re-try building blocks.
- This adds a new tip-selection algorithm that minimizes block orphans within a
  configurable window of time.
- When configured, the node will automatically stop mining if it is not achieving a
  targeted win rate over a configurable window of blocks.
- When configured, the node will selectively mine transactions from only certain
  addresses, or only of certain types (STX-transfers, contract-publishes,
  contract-calls).
- When configured, the node will optionally only RBF block-commits if it can
  produce a block with strictly more transactions.

### Changed

- `developer-mode` is no longer enabled in the default feature set. This is the correct default behavior, since the stacks-node should NOT build with developer-mode enabled by default. Tools that need to use developer-mode should enable it explicitly.

### Fixed

- The transaction receipts for smart contract publish transactions now indicate
  a result of `(err none)` if the top-level code of the smart contract contained
  runtime error and include details about the error in the `vm_error` field of
  the receipt. Fixes issues #3154, #3328.
- Added config setting `burnchain.wallet_name` which addresses blank wallets no
  longer being created by default in recent bitcoin versions. Fixes issue #3596
- Use the current burnchain tip to lookup UTXOs (Issue #3733)
- The node now gracefully shuts down even if it is in the middle of a handshake with
  bitcoind. Fixes issue #3734.

## [2.4.0.0.4]

This is a high-priority hotfix that addresses a bug in transaction processing which
could impact miner availability.

## [2.4.0.0.3]

This is a high-priority hotfix that addresses a bug in transaction processing which
could impact miner availability.

## [2.4.0.0.2]

This is a hotfix that changes the logging failure behavior from panicking to dropping
the log message (PR #3784).

## [2.4.0.0.4]

This is a high-priority hotfix that addresses a bug in transaction processing which
could impact miner availability.

## [2.4.0.0.3]

This is a high-priority hotfix that addresses a bug in transaction processing which
could impact miner availability.

## [2.4.0.0.2]

This is a hotfix that changes the logging failure behavior from panicking to dropping
the log message (PR #3784).

## [2.4.0.0.1]

This is a minor change to add `txid` fields into the log messages from failing
contract deploys. This will help tools (and users) more easily find the log
messages to determine what went wrong.

## [2.4.0.0.0]

This is a **consensus-breaking** release to revert consensus to PoX, and is the second fork proposed in SIP-022.

- [SIP-022](https://github.com/stacksgov/sips/blob/main/sips/sip-022/sip-022-emergency-pox-fix.md)
- [SIP-024](https://github.com/stacksgov/sips/blob/main/sips/sip-024/sip-024-least-supertype-fix.md)

### Fixed

- PoX is re-enabled and stacking resumes starting at Bitcoin block `791551`
- Peer network id is updated to `0x18000009`
- Adds the type sanitization described in SIP-024

This release is compatible with chainstate directories from 2.1.0.0.x and 2.3.0.0.x

## [2.3.0.0.2]

This is a high-priority hotfix release to address a bug in the
stacks-node miner logic which could impact miner availability.

This release is compatible with chainstate directories from 2.3.0.0.x and 2.1.0.0.x

## [2.3.0.0.1]

This is a hotfix release to update:

- peer version identifier used by the stacks-node p2p network.
- yield interpreter errors in deser_hex

This release is compatible with chainstate directories from 2.3.0.0.x and 2.1.0.0.x

## [2.3.0.0.0]

This is a **consensus-breaking** release to address a Clarity VM bug discovered in 2.2.0.0.1.
Tx and read-only calls to functions with traits as parameters are rejected with unchecked TypeValueError.
Additional context and rationale can be found in [SIP-023](https://github.com/stacksgov/sips/blob/main/sips/sip-023/sip-023-emergency-fix-traits.md).

This release is compatible with chainstate directories from 2.1.0.0.x.

## [2.2.0.0.1]

This is a **consensus-breaking** release to address a bug and DoS vector in pox-2's `stack-increase` function.
Additional context and rationale can be found in [SIP-022](https://github.com/stacksgov/sips/blob/main/sips/sip-022/sip-022-emergency-pox-fix.md).

This release is compatible with chainstate directories from 2.1.0.0.x.

## [2.1.0.0.3]

This is a high-priority hotfix release to address a bug in the
stacks-node miner logic which could impact miner availability. This
release's chainstate directory is compatible with chainstate
directories from 2.1.0.0.2.

## [2.1.0.0.2]

This software update is a hotfix to resolve improper unlock handling
in mempool admission. This release's chainstate directory is
compatible with chainstate directories from 2.1.0.0.1.

### Fixed

- Fix mempool admission logic's improper handling of PoX unlocks. This would
  cause users to get spurious `NotEnoughFunds` rejections when trying to submit
  their transactions (#3623)

## [2.1.0.0.1]

### Fixed

- Handle the case where a bitcoin node returns zero headers (#3588)
- The default value for `always_use_affirmation_maps` is now set to `false`,
  instead of `true`. This was preventing testnet nodes from reaching the chain
  tip with the default configuration.
- Reduce default poll time of the `chain-liveness` thread which reduces the
  possibility that a miner thread will get interrupted (#3610).

## [2.1]

This is a **consensus-breaking** release that introduces a _lot_ of new
functionality. Details on the how and why can be found in [SIP-015](https://github.com/stacksgov/sips/blob/feat/sip-015/sips/sip-015/sip-015-network-upgrade.md),
[SIP-018](https://github.com/MarvinJanssen/sips/blob/feat/signed-structured-data/sips/sip-018/sip-018-signed-structured-data.md),
and [SIP-20](https://github.com/obycode/sips/blob/bitwise-ops/sips/sip-020/sip-020-bitwise-ops.md).

The changelog for this release is a high-level summary of these SIPs.

### Added

- There is a new `.pox-2` contract for implementing proof-of-transfer. This PoX
  contract enables re-stacking while the user's STX are locked, and incrementing
  the amount stacked on top of a locked batch of STX.
- The Clarity function `stx-account` has been added, which returns the account's
  locked and unlocked balances.
- The Clarity functions `principal-destruct` and `principal-construct?`
  functions have been added, which provide the means to convert between a
  `principal` instance and the `buff`s and `string-ascii`s that constitute it.
- The Clarity function `get-burn-block-info?` has been added to support
  fetching the burnchain header hash of _any_ burnchain block starting from the
  sortition height of the Stacks genesis block, and to support fetching the PoX
  addresses and rewards paid by miners for a particular burnchain block height.
- The Clarity function `slice` has been added for obtaining a sub-sequence of a
  `buff`, `string-ascii`, `string-utf8`, or `list`.
- Clarity functions for converting between `string-ascii`, `string-utf8`,
  `uint`, and `int` have been added.
- Clarity functions for converting between big- and little-endian
  `buff` representations of `int` and `uint` have been added.
- The Clarity function `stx-transfer-memo?` has been added, which behaves the
  same as `stx-transfer?` but also takes a memo argument.
- The Clarity function `is-standard` has been added to identify whether or not a
  `principal` instance is a standard or contract principal.
- Clarity functions have been added for converting an arbitrary Clarity type to
  and from its canonical byte string representation.
- The Clarity function `replace-at?` has been added for replacing a single item
  in a `list`, `string-ascii`, `string-utf8`, or `buff`.
- The Clarity global variable `tx-sponsor?` has been added, which evaluates to
  the sponsor of the transaction if the transaction is sponsored.
- The Clarity global variable `chain-id` has been added, which evaluates to the
  4-byte chain ID of this Stacks network.
- The Clarity parser has been rewritten to be about 3x faster than the parser in
  Stacks 2.05.x.x.x.
- Clarity trait semantics have been refined and made more explicit, so as to
  avoid certain corner cases where a trait reference might be downgraded to a
  `principal` in Clarity 1.
  - Trait values can be passed to compatible sub-trait types
  - Traits can be embedded in compound types, e.g. `(optional <my-trait>)`
  - Traits can be assigned to a let-variable
- Fixes to unexpected behavior in traits
  - A trait with duplicate function names is now an error
  - Aliased trait names do not interfere with local trait definitions
- The comparison functions `<`, `<=`, `>`, and `>=` now work on `string-ascii`,
  `string-utf8`, and `buff` based on byte-by-byte comparison (note that this is
  _not_ lexicographic comparison).
- It is now possible to call `delegate-stx` from a burnchain transaction, just
  as it is for `stack-stx` and `transfer-stx`.

### Changed

- The `delegate-stx` function in `.pox-2` can be called while the user's STX are
  locked.
- If a batch of STX is not enough to clinch even a single reward slot, then the
  STX are automatically unlocked at the start of the reward cycle in which they
  are rendered useless in this capacity.
- The PoX sunset has been removed. PoX rewards will continue in perpetuity.
- Support for segwit and taproot addresses (v0 and v1 witness programs) has been
  added for Stacking.
- The Clarity function `get-block-info?` now supports querying a block's total
  burnchain spend by miners who tried to mine it, the spend by the winner, and
  the total block reward (coinbase plus transaction fees).
- A block's coinbase transaction may specify an alternative recipient principal,
  which can be either a standard or contract principal.
- A smart contract transaction can specify which version of Clarity to use. If
  no version is given, then the epoch-default version will be used (in Stacks
  2.1, this is Clarity 2).
- The Stacks node now includes the number of PoX anchor blocks in its
  fork-choice rules. The best Stacks fork is the fork that (1) is on the best
  Bitcoin fork, (2) has the most PoX anchor blocks known, and (3) is the longest.
- On-burnchain operations -- `stack-stx`, `delegate-stx`, and `transfer-stx` --
  can take effect within six (6) burnchain blocks in which they are mined,
  instead of one.
- Transaction fees are debited from accounts _before_ the transaction is
  processed.
- All smart contract analysis errors are now treated as runtime errors, meaning
  that smart contract transactions which don't pass analysis will still be mined
  (so miners get paid for partially validating them).
- The default Clarity version is now 2. Users can opt for version 1 by using
  the new smart contract transaction wire format and explicitly setting version

### Fixed

- The authorization of a `contract-caller` in `.pox-2` for stacking will now
  expire at the user-specified height, if given.
- The Clarity function `principal-of?` now works on mainnet.
- One or more late block-commits no longer result in the miner losing its
  sortition weight.
- Documentation will indicate explicitly which Clarity version introduced each
  keyword or function.

## [2.05.0.6.0]

### Changed

- The `/v2/neighbors` endpoint now reports a node's bootstrap peers, so other
  nodes can find high-quality nodes to boot from (#3401)
- If there are two or more Stacks chain tips that are tied for the canonical
  tip, the node deterministically chooses one _independent_ of the arrival order
  (#3419).
- If Stacks blocks for a different fork arrive out-of-order and, in doing so,
  constitute a better fork than the fork the node considers canonical, the node
  will update the canonical Stacks tip pointer in the sortition DB before
  processing the next sortition (#3419).

### Fixed

- The node keychain no longer maintains any internal state, but instead derives
  keys based on the chain tip the miner is building off of. This prevents the
  node from accidentally producing an invalid block that reuses a microblock
  public key hash (#3387).
- If a node mines an invalid block for some reason, it will no longer stall
  forever. Instead, it will detect that its last-mined block is not the chain
  tip, and resume mining (#3406).

## [2.05.0.5.0]

### Changed

- The new minimum Rust version is 1.61
- The act of walking the mempool will now cache address nonces in RAM and to a
  temporary mempool table used for the purpose, instead of unconditionally
  querying them from the chainstate MARF. This builds upon improvements to mempool
  goodput over 2.05.0.4.0 (#3337).
- The node and miner implementation has been refactored to remove write-lock
  contention that can arise when the node's chains-coordinator thread attempts to store and
  process newly-discovered (or newly-mined) blocks, and when the node's relayer
  thread attempts to mine a new block. In addition, the miner logic has been
  moved to a separate thread in order to avoid starving the relayer thread (which
  must handle block and transaction propagation, as well as block-processing).
  The refactored miner thread will be preemptively terminated and restarted
  by the arrival of new Stacks blocks or burnchain blocks, which further
  prevents the miner from holding open write-locks in the underlying
  chainstate databases when there is new chain data to discover (which would
  invalidate the miner's work anyway). (#3335).

### Fixed

- Fixed `pow` documentation in Clarity (#3338).
- Backported unit tests that were omitted in the 2.05.0.3.0 release (#3348).

## [2.05.0.4.0]

### Fixed

- Denormalize the mempool database so as to remove a `LEFT JOIN` from the SQL
  query for choosing transactions in order by estimated fee rate. This
  drastically speeds up mempool transaction iteration in the miner (#3314)

## [2.05.0.3.0]

### Added

- Added prometheus output for "transactions in last block" (#3138).
- Added environment variable STACKS_LOG_FORMAT_TIME to set the time format
  stacks-node uses for logging. (#3219)
  Example: STACKS_LOG_FORMAT_TIME="%Y-%m-%d %H:%M:%S" cargo stacks-node
- Added mock-miner sample config (#3225)

### Changed

- Updates to the logging of transaction events (#3139).
- Moved puppet-chain to `./contrib/tools` directory and disabled compiling by default (#3200)

### Fixed

- Make it so that a new peer private key in the config file will propagate to
  the peer database (#3165).
- Fixed default miner behavior regarding block assembly
  attempts. Previously, the miner would only attempt to assemble a
  larger block after their first attempt (by Bitcoin RBF) if new
  microblock or block data arrived. This changes the miner to always
  attempt a second block assembly (#3184).
- Fixed a bug in the node whereby the node would encounter a deadlock when
  processing attachment requests before the P2P thread had started (#3236).
- Fixed a bug in the P2P state machine whereby it would not absorb all transient errors
  from sockets, but instead propagate them to the outer caller. This would lead
  to a node crash in nodes connected to event observers, which expect the P2P
  state machine to only report fatal errors (#3228)
- Spawn the p2p thread before processing number of sortitions. Fixes issue (#3216) where sync from genesis paused (#3236)
- Drop well-formed "problematic" transactions that result in miner performance degradation (#3212)
- Ignore blocks that include problematic transactions

## [2.05.0.2.1]

### Fixed

- Fixed a security bug in the SPV client whereby the chain work was not being
  considered at all when determining the canonical Bitcoin fork. The SPV client
  now only accepts a new Bitcoin fork if it has a higher chain work than any other
  previously-seen chain (#3152).

## [2.05.0.2.0]

### IMPORTANT! READ THIS FIRST

Please read the following **WARNINGs** in their entirety before upgrading.

WARNING: Please be aware that using this node on chainstate prior to this release will cause
the node to spend **up to 30 minutes** migrating the data to a new schema.
Depending on the storage medium, this may take even longer.

WARNING: This migration process cannot be interrupted. If it is, the chainstate
will be **irrecovarably corrupted and require a sync from genesis.**

WARNING: You will need **at least 2x the disk space** for the migration to work.
This is because a copy of the chainstate will be made in the same directory in
order to apply the new schema.

It is highly recommended that you **back up your chainstate** before running
this version of the software on it.

### Changed

- The MARF implementation will now defer calculating the root hash of a new trie
  until the moment the trie is committed to disk. This avoids gratuitous hash
  calculations, and yields a performance improvement of anywhere between 10x and
  200x (#3041).
- The MARF implementation will now store tries to an external file for instances
  where the tries are expected to exceed the SQLite page size (namely, the
  Clarity database). This improves read performance by a factor of 10x to 14x
  (#3059).
- The MARF implementation may now cache trie nodes in RAM if directed to do so
  by an environment variable (#3042).
- Sortition processing performance has been improved by about an order of
  magnitude, by avoiding a slew of expensive database reads (#3045).
- Updated chains coordinator so that before a Stacks block or a burn block is processed,
  an event is sent through the event dispatcher. This fixes #3015.
- Expose a node's public key and public key hash160 (i.e. what appears in
  /v2/neighbors) via the /v2/info API endpoint (#3046)
- Reduced the default subsequent block attempt timeout from 180 seconds to 30
  seconds, based on benchmarking the new MARF performance data during a period
  of network congestion (#3098)
- The `blockstack-core` binary has been renamed to `stacks-inspect`.
  This binary provides CLI tools for chain and mempool inspection.

### Fixed

- The AtlasDB previously could lose `AttachmentInstance` data during shutdown
  or crashes (#3082). This release resolves that.

## [2.05.0.1.0]

### Added

- A new fee estimator intended to produce fewer over-estimates, by having less
  sensitivity to outliers. Its characteristic features are: 1) use a window to
  forget past estimates instead of exponential averaging, 2) use weighted
  percentiles, so that bigger transactions influence the estimates more, 3)
  assess empty space in blocks as having paid the "minimum fee", so that empty
  space is accounted for, 4) use random "fuzz" so that in busy times the fees can
  change dynamically. (#2972)
- Implements anti-entropy protocol for querying transactions from other
  nodes' mempools. Before, nodes wouldn't sync mempool contents with one another.
  (#2884)
- Structured logging in the mining code paths. This will shine light
  on what happens to transactions (successfully added, skipped or errored) that the
  miner considers while buildings blocks. (#2975)
- Added the mined microblock event, which includes information on transaction
  events that occurred in the course of mining (will provide insight
  on whether a transaction was successfully added to the block,
  skipped, or had a processing error). (#2975)
- For v2 endpoints, can now specify the `tip` parameter to `latest`. If
  `tip=latest`, the node will try to run the query off of the latest tip. (#2778)
- Adds the /v2/headers endpoint, which returns a sequence of SIP-003-encoded
  block headers and consensus hashes (see the ExtendedStacksHeader struct that
  this PR adds to represent this data). (#2862)
- Adds the /v2/data_var endpoint, which returns a contract's data variable
  value and a MARF proof of its existence. (#2862)
- Fixed a bug in the unconfirmed state processing logic that could lead to a
  denial of service (node crash) for nodes that mine microblocks (#2970)
- Added prometheus metric that tracks block fullness by logging the percentage of each
  cost dimension that is consumed in a given block (#3025).

### Changed

- Updated the mined block event. It now includes information on transaction
  events that occurred in the course of mining (will provide insight
  on whether a transaction was successfully added to the block,
  skipped, or had a processing error). (#2975)
- Updated some of the logic in the block assembly for the miner and the follower
  to consolidate similar logic. Added functions `setup_block` and `finish_block`.
  (#2946)
- Makes the p2p state machine more reactive to newly-arrived
  `BlocksAvailable` and `MicroblocksAvailable` messages for block and microblock
  streams that this node does not have. If such messages arrive during an inventory
  sync, the p2p state machine will immediately transition from the inventory sync
  work state to the block downloader work state, and immediately proceed to fetch
  the available block or microblock stream. (#2862)
- Nodes will push recently-obtained blocks and microblock streams to outbound
  neighbors if their cached inventories indicate that they do not yet have them
  (#2986).
- Nodes will no longer perform full inventory scans on their peers, except
  during boot-up, in a bid to minimize block-download stalls (#2986).
- Nodes will process sortitions in parallel to downloading the Stacks blocks for
  a reward cycle, instead of doing these tasks sequentially (#2986).
- The node's runloop will coalesce and expire stale requests to mine blocks on
  top of parent blocks that are no longer the chain tip (#2969).
- Several database indexes have been updated to avoid table scans, which
  significantly improves most RPC endpoint speed and cuts node spin-up time in
  half (#2989, #3005).
- Fixed a rare denial-of-service bug whereby a node that processes a very deep
  burnchain reorg can get stuck, and be rendered unable to process further
  sortitions. This has never happened in production, but it can be replicated in
  tests (#2989).
- Updated what indices are created, and ensures that indices are created even
  after the database is initialized (#3029).

### Fixed

- Updates the lookup key for contracts in the pessimistic cost estimator. Before, contracts
  published by different principals with the same name would have had the same
  key in the cost estimator. (#2984)
- Fixed a few prometheus metrics to be more accurate compared to `/v2` endpoints
  when polling data (#2987)
- Fixed an error message from the type-checker that shows up when the type of a
  parameter refers to a trait defined in the same contract (#3064).

## [2.05.0.0.0]

This software update is a consensus changing release and the
implementation of the proposed cost changes in SIP-012. This release's
chainstate directory is compatible with chainstate directories from
2.0.11.4.0. However, this release is only compatible with chainstate
directories before the 2.05 consensus changes activate (Bitcoin height
713,000). If you run a 2.00 stacks-node beyond this point, and wish to
run a 2.05 node afterwards, you must start from a new chainstate
directory.

### Added

- At height 713,000 a new `costs-2` contract will be launched by the
  Stacks boot address.

### Changed

- Stacks blocks whose parents are mined >= 713,000 will use default costs
  from the new `costs-2` contract.
- Stacks blocks whose parents are mined >= 713,000 will use the real
  serialized length of Clarity values as the cost inputs to several methods
  that previously used the maximum possible size for the associated types.
- Stacks blocks whose parents are mined >= 713,000 will use the new block
  limit defined in SIP-012.

### Fixed

- Miners are now more aggressive in calculating their block limits
  when confirming microblocks (#2916)

## [2.0.11.4.0]

This software update is a point-release to change the transaction
selection logic in the default miner to prioritize by an estimated fee
rate instead of raw fee. This release's chainstate directory is
compatible with chainstate directories from 2.0.11.3.0.

### Added

- FeeEstimator and CostEstimator interfaces. These can be controlled
  via node configuration options. See the `README.md` for more
  information on the configuration.
- New fee rate estimation endpoint `/v2/fees/transaction` (#2872). See
  `docs/rpc/openapi.yaml` for more information.

### Changed

- Prioritize transaction inclusion in blocks by estimated fee rates (#2859).
- MARF sqlite connections will now use `mmap`'ed connections with up to 256MB
  space (#2869).

## [2.0.11.3.0]

This software update is a point-release to change the transaction selection
logic in the default miner to prioritize by fee instead of nonce sequence. This
release's chainstate directory is compatible with chainstate directories from
2.0.11.2.0.

## Added

- The node will enforce a soft deadline for mining a block, so that a node
  operator can control how frequently their node attempts to mine a block
  regardless of how congested the mempool is. The timeout parameters are
  controlled in the `[miner]` section of the node's config file (#2823).

## Changed

- Prioritize transaction inclusion in the mempool by transaction fee (#2823).

## [2.0.11.2.0]

NOTE: This change resets the `testnet`. Users running a testnet node will need
to reset their chain states.

### Added

- `clarity-cli` will now also print a serialized version of the resulting
  output from `eval` and `execute` commands. This serialization is in
  hexademical string format and supports integration with other tools. (#2684)
- The creation of a Bitcoin wallet with BTC version `> 0.19` is now supported
  on a private testnet. (#2647)
- `lcov`-compatible coverage reporting has been added to `clarity-cli` for
  Clarity contract testing. (#2592)
- The `README.md` file has new documentation about the release process. (#2726)

### Changed

- This change resets the testnet. (#2742)
- Caching has been added to speed up `/v2/info` responses. (#2746)

### Fixed

- PoX syncing will only look back to the reward cycle prior to divergence,
  instead of looking back over all history. This will speed up running a
  follower node. (#2746)
- The UTXO staleness check is re-ordered so that it occurs before the RBF-limit
  check. This way, if stale UTXOs reached the "RBF limit" a miner will recover
  by resetting the UTXO cache. (#2694)
- Microblock events were being sent to the event observer when microblock data
  was received by a peer, but were not emitted if the node mined the
  microblocks itself. This made something like the private-testnet setup
  incapable of emitting microblock events. Microblock events are now sent
  even when self-mined. (#2653)
- A bug is fixed in the mocknet/helium miner that would lead to a panic if a
  burn block occurred without a sortition in it. (#2711)
- Two bugs that caused problems syncing with the bitcoin chain during a
  bitcoin reorg have been fixed (#2771, #2780).
- Documentation is fixed in cases where string and buffer types are allowed
  but not covered in the documentation. (#2676)

## [2.0.11.1.0]

This software update is our monthly release. It introduces fixes and features for both developers and miners.
This release's chainstate directory is compatible with chainstate directories from 2.0.11.0.0.

## Added

- `/new_microblock` endpoint to notify event observers when a valid microblock
  has been received (#2571).
- Added new features to `clarity-cli` (#2597)
- Exposing new mining-related metrics in prometheus (#2664)
  - Miner's computed relative miner score as a percentage
  - Miner's computed commitment, the min of their previous commitment and their median commitment
  - Miner's current median commitment
- Add `key-for-seed` command to the `stacks-node` binary - outputs the associated secret key hex string
  and WIF formatted secret key for a given "seed" value (#2658).

## Changed

- Improved mempool walk order (#2514).
- Renamed database `tx_tracking.db` to `tx_tracking.sqlite` (#2666).

## Fixed

- Alter the miner to prioritize spending the most recent UTXO when building a transaction,
  instead of the largest UTXO. In the event of a tie, it uses the smallest UTXO first (#2661).
- Fix trait rpc lookups for implicitly implemented traits (#2602).
- Fix `v2/pox` endpoint, broken on Mocknet (#2634).
- Align cost limits on mocknet, testnet and mainnet (#2660).
- Log peer addresses in the HTTP server (#2667)
- Mine microblocks if there are no recent unprocessed Stacks blocks

## [2.0.11.0.0]

The chainstate directory has been restructured in this release. It is not
compatible with prior chainstate directories.

## Added

- `/drop_mempool_tx` endpoint to notify event observers when a mempool
  transaction has been removed the mempool.
- `"reward_slot_holders"` field to the `new_burn_block` event
- CTRL-C handler for safe shutdown of `stacks-node`
- Log transactions in local db table via setting env `STACKS_TRANSACTION_LOG=1`
- New prometheus metrics for mempool transaction processing times and
  outstanding mempool transactions
- New RPC endpoint with path `/v2/traits/contractAddr/contractName/traitContractName
/traitContractAddr/traitName` to determine whether a given trait is implemented
  within the specified contract (either explicitly or implicitly).
- Re-activate the Atlas network for propagating and storing transaction
  attachments. This re-enables off-chain BNS name storage.
- Re-activate microblock mining.

## Changed

- Improved chainstate directory layout
- Improved node boot up time
- Better handling of flash blocks
- The `/v2/pox` RPC endpoint was updated to include more useful
  information about the current and next PoX cycles. For details, see
  `docs/rpc-endpoints.md`

## Fixed

- Fixed faulty logic in the mempool that was still treating the transaction fee
  as a fee rate, which prevented replace-by-fee from working as expected.

## [2.0.10.0.1]

This is a low-priority hotfix release to address a bug in the deserialization logic. The
chainstate directory of 2.0.10.0.1 is compatible with 2.0.10. This release also begins the
usage of the versioning scheme outlined in the [README.md](README.md).

## [2.0.10]

This is a low-priority hotfix release to address two bugs in the block downloader. The
chainstate directory of 2.0.10 is compatible with 2.0.9. If booting up a node from genesis, or
an existing node has stalled in downloading blocks, this hotfix is necessary for your
node.

## Fixed

- Bug in microblocks inventory vector calculation that included invalidated microblocks
  as present bit. This bug will impact nodes booting up from genesis, but not affect nodes
  currently running at the chain tip (#2518).
- Bug in microblocks downloader logic that would cause the stacks-node to fail to wake-up
  to process newly arrived microblocks in certain instances (#2491).

## [2.0.9]

This is a hotfix release for improved handling of arriving Stacks blocks through
both the RPC interface and the P2P ineterface. The chainstate directory of
2.0.9 is compatible with the 2.0.8 chainstate.

## Fixed

- TOCTTOU bug fixed in the chain processing logic that, which now ensures that
  an arriving Stacks block is processed at most once.

## [2.0.8] - 2021-03-02

This is a hotfix release for improved handling of static analysis storage and
improved `at-block` behavior. The chainstate directory of 2.0.8 is compatible with
the 2.0.7 chainstate.

## Fixed

- Improved static analysis storage
- `at-block` behavior in `clarity-cli` and unit tests (no changes in `stacks-node`
  behavior).

## [2.0.7] - 2021-02-26

This is an emergency hotfix that prevents the node from accidentally deleting
valid block data if its descendant microblock stream is invalid for some reason.

## Fixed

- Do not delete a valid parent Stacks block.

## [2.0.6] - 2021-02-15

The database schema has not changed since 2.0.5, so when spinning up a
2.0.6 node from a 2.0.5 chainstate, you do not need to use a fresh
working directory. Earlier versions' chainstate directories are
incompatible, however.

### Fixed

- Miner RBF logic has two "fallback" logic changes. First, if the RBF
  logic has increased fees by more than 50%, do not submit a new
  transaction. Second, fix the "same chainstate hash" fallback check.
- Winning block txid lookups in the SortitionDB have been corrected
  to use the txid during the lookup.
- The miner will no longer attempt to mine a new Stacks block if it receives a
  microblock in a discontinuous microblock stream.

## [2.0.5] - 2021-02-12

The database schema has changed since 2.0.4, so when spinning up a 2.0.5
node from an earlier chainstate, you must use a fresh working directory.

### Added

- Miner heuristic for handling relatively large or computationally
  expensive transactions: such transactions will be dropped from the
  mempool to prevent miners from re-attempting them once they fail.
  Miners can also now continue processing transactions that are
  behind those transactions in the mempool "queue".

### Fixed

- Miner block assembly now uses the correct block limit available via
  the node config
- `tx_fees_streamed_produced` fees are included in miner coinbase
  events for event observers
- SQLite indexes are now correctly created on database instantion

### Changed

- STX unlock events are now sent over the events endpoint bundled
  into an associated unlock transaction
- Atlas attachments networking endpoints are disabled for this
  release, while networking issues are addressed in the
  implementation

## [2.0.4] - 2021-02-07

### Changed

- Atlas attachments networking endpoints are disabled for this
  release, while networking issues are addressed in the
  implementation.

## [2.0.3] - 2021-02-04

### Added

- `stacks-node --mine-at-height` commandline option, which tells the
  `stacks-node` not to mine until it has synchronized to the given
  Stacks block height
- A new RPC endpoint `/v2/blocks/upload/{consensus_hash}` that accepts
  an uploaded a Stacks block for a given sortition

### Changed

- Enabled WAL mode for the chainstate databases. This allows much more
  concurrency in the `stacks-node`, and improves network performance
  across the board. **NOTE:** _This changed the database schema, any
  running node would need to re-initialize their nodes from a new chain
  state when upgrading_.
- Default value `wait_time_for_microblocks`: from 60s to 30s
- The mempool now performs more transfer semantics checks before admitting
  a transaction (e.g., reject if origin = recipient): see issue #2354
- Improved the performance of the code that handles `GetBlocksInv` p2p
  messages by an order of magnitude.
- Improved the performance of the block-downloader's block and
  microblock search code by a factor of 5x.

### Fixed

- Miner mempool querying now works across short-lived forks: see issue #2389
- JSON deserialization for high-depth JSON objects
- Atlas attachment serving: see PR #2390
- Address issues #2379, #2356, #2347, #2346. The tracking of the
  `LeaderBlockCommit` operations inflight is improved, drastically
  reducing the number of block commit rejections. When
  a`LeaderBlockCommit` is not included in the Bitcoin block it was
  targeting, it is condemned to be rejected, per the Stacks
  consensus. To avoid wasting BTC, the miner now tries to send its
  next `LeaderBlockCommit` operations using the UTXOs of the previous
  transaction with a replacement by fee. The fee increase increments
  can be configured with the setting `rbf_fee_increment`.
