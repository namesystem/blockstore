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

use std::char::from_digit;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::io::{BufWriter, Cursor, Read, Seek, SeekFrom, Write};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use std::{cmp, env, error, fmt, fs, io, os};

use rusqlite::types::{FromSql, ToSql};
use rusqlite::{
    Connection, Error as SqliteError, ErrorCode as SqliteErrorCode, OpenFlags, OptionalExtension,
    Transaction,
};
use sha2::Digest;
use stacks_common::types::chainstate::{
    BlockHeaderHash, TrieHash, BLOCK_HEADER_HASH_ENCODED_SIZE, TRIEHASH_ENCODED_SIZE,
};
use stacks_common::types::sqlite::NO_PARAMS;
use stacks_common::util::hash::to_hex;
use stacks_common::util::log;

use crate::chainstate::stacks::index::bits::{
    get_node_byte_len, get_node_hash, read_block_identifier, read_hash_bytes, read_node_hash_bytes,
    read_nodetype, read_root_hash, write_nodetype_bytes,
};
use crate::chainstate::stacks::index::cache::*;
use crate::chainstate::stacks::index::file::{TrieFile, TrieFileNodeHashReader};
use crate::chainstate::stacks::index::marf::MARFOpenOpts;
use crate::chainstate::stacks::index::node::{
    clear_backptr, is_backptr, set_backptr, TrieNode, TrieNode16, TrieNode256, TrieNode4,
    TrieNode48, TrieNodeID, TrieNodeType, TriePtr,
};
use crate::chainstate::stacks::index::profile::TrieBenchmark;
use crate::chainstate::stacks::index::trie::Trie;
use crate::chainstate::stacks::index::{
    trie_sql, BlockMap, ClarityMarfTrieId, Error, MarfTrieId, TrieHasher, TrieLeaf,
};
use crate::util_lib::db::{
    sql_pragma, sqlite_open, tx_begin_immediate, tx_busy_handler, Error as db_error,
    SQLITE_MARF_PAGE_SIZE, SQLITE_MMAP_SIZE,
};

/// A trait for reading the hash of a node into a given Write impl, given the pointer to a node in
/// a trie.
pub trait NodeHashReader {
    fn read_node_hash_bytes<W: Write>(&mut self, ptr: &TriePtr, w: &mut W) -> Result<(), Error>;
}

impl<T: MarfTrieId> BlockMap for TrieFileStorage<T> {
    type TrieId = T;

    fn get_block_hash(&self, id: u32) -> Result<T, Error> {
        trie_sql::get_block_hash(&self.db, id)
    }

    fn get_block_hash_caching(&mut self, id: u32) -> Result<&T, Error> {
        if !self.is_block_hash_cached(id) {
            let block_hash = self.get_block_hash(id)?;
            self.cache.store_block_hash(id, block_hash);
        }
        self.cache.ref_block_hash(id).ok_or(Error::NotFoundError)
    }

    fn is_block_hash_cached(&self, id: u32) -> bool {
        self.cache.ref_block_hash(id).is_some()
    }

    fn get_block_id(&self, block_hash: &T) -> Result<u32, Error> {
        trie_sql::get_block_identifier(&self.db, block_hash)
    }

    fn get_block_id_caching(&mut self, block_hash: &T) -> Result<u32, Error> {
        // don't use the cache if we're unconfirmed
        if self.data.unconfirmed {
            self.get_block_id(block_hash)
        } else if let Some(block_id) = self.cache.load_block_id(block_hash) {
            Ok(block_id)
        } else {
            let block_id = self.get_block_id(block_hash)?;
            self.cache.store_block_hash(block_id, block_hash.clone());
            Ok(block_id)
        }
    }
}

impl<T: MarfTrieId> BlockMap for TrieStorageConnection<'_, T> {
    type TrieId = T;

    fn get_block_hash(&self, id: u32) -> Result<T, Error> {
        trie_sql::get_block_hash(&self.db, id)
    }

    fn get_block_hash_caching(&mut self, id: u32) -> Result<&T, Error> {
        if !self.is_block_hash_cached(id) {
            let block_hash = self.get_block_hash(id)?;
            self.cache.store_block_hash(id, block_hash);
        }
        self.cache.ref_block_hash(id).ok_or(Error::NotFoundError)
    }

    fn is_block_hash_cached(&self, id: u32) -> bool {
        self.cache.ref_block_hash(id).is_some()
    }

    fn get_block_id(&self, block_hash: &T) -> Result<u32, Error> {
        trie_sql::get_block_identifier(&self.db, block_hash)
    }

    fn get_block_id_caching(&mut self, block_hash: &T) -> Result<u32, Error> {
        // don't use the cache if we're unconfirmed
        if self.data.unconfirmed {
            self.get_block_id(block_hash)
        } else if let Some(block_id) = self.cache.load_block_id(block_hash) {
            Ok(block_id)
        } else {
            let block_id = self.get_block_id(block_hash)?;
            self.cache.store_block_hash(block_id, block_hash.clone());
            Ok(block_id)
        }
    }
}

impl<T: MarfTrieId> BlockMap for TrieStorageTransaction<'_, T> {
    type TrieId = T;

    fn get_block_hash(&self, id: u32) -> Result<T, Error> {
        self.deref().get_block_hash(id)
    }

    fn get_block_hash_caching(&mut self, id: u32) -> Result<&T, Error> {
        self.deref_mut().get_block_hash_caching(id)
    }

    fn is_block_hash_cached(&self, id: u32) -> bool {
        self.deref().is_block_hash_cached(id)
    }

    fn get_block_id(&self, block_hash: &T) -> Result<u32, Error> {
        self.deref().get_block_id(block_hash)
    }

    fn get_block_id_caching(&mut self, block_hash: &T) -> Result<u32, Error> {
        self.deref_mut().get_block_id_caching(block_hash)
    }
}

impl<T: MarfTrieId> BlockMap for TrieSqlHashMapCursor<'_, T> {
    type TrieId = T;

    fn get_block_hash(&self, id: u32) -> Result<T, Error> {
        trie_sql::get_block_hash(self.db, id)
    }

    fn get_block_hash_caching(&mut self, id: u32) -> Result<&T, Error> {
        if !self.is_block_hash_cached(id) {
            let block_hash = self.get_block_hash(id)?;
            self.cache.store_block_hash(id, block_hash);
        }
        self.cache.ref_block_hash(id).ok_or(Error::NotFoundError)
    }

    fn is_block_hash_cached(&self, id: u32) -> bool {
        self.cache.ref_block_hash(id).is_some()
    }

    fn get_block_id(&self, block_hash: &T) -> Result<u32, Error> {
        trie_sql::get_block_identifier(self.db, block_hash)
    }

    fn get_block_id_caching(&mut self, block_hash: &T) -> Result<u32, Error> {
        // don't use the cache if we're unconfirmed
        if self.unconfirmed {
            self.get_block_id(block_hash)
        } else if let Some(block_id) = self.cache.load_block_id(block_hash) {
            Ok(block_id)
        } else {
            let block_id = self.get_block_id(block_hash)?;
            self.cache.store_block_hash(block_id, block_hash.clone());
            Ok(block_id)
        }
    }
}

enum FlushOptions<'a, T: MarfTrieId> {
    CurrentHeader,
    NewHeader(&'a T),
    MinedTable(&'a T),
    UnconfirmedTable,
}

impl<T: MarfTrieId> fmt::Display for FlushOptions<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FlushOptions::CurrentHeader => write!(f, "self"),
            FlushOptions::MinedTable(bhh) => write!(f, "{}.mined", bhh),
            FlushOptions::NewHeader(bhh) => write!(f, "{}", bhh),
            FlushOptions::UnconfirmedTable => write!(f, "self.unconfirmed"),
        }
    }
}

/// Uncommitted storage state to be flushed
#[derive(Clone)]
pub enum UncommittedState<T: MarfTrieId> {
    /// read-write
    RW(TrieRAM<T>),
    /// read-only, sealed, with root hash
    Sealed(TrieRAM<T>, TrieHash),
}

impl<T: MarfTrieId> UncommittedState<T> {
    /// Clear the contents
    pub fn format(&mut self) -> Result<(), Error> {
        match self {
            UncommittedState::RW(ref mut trie_ram) => trie_ram.format(),
            _ => {
                panic!("FATAL: cannot format a sealed TrieRAM");
            }
        }
    }

    /// Get a hint as to how big the uncommitted state is
    pub fn size_hint(&self) -> usize {
        match self {
            UncommittedState::RW(ref trie_ram) => trie_ram.size_hint(),
            UncommittedState::Sealed(ref trie_ram, _) => trie_ram.size_hint(),
        }
    }

    /// Get an immutable reference to the inner TrieRAM
    pub fn trie_ram_ref(&self) -> &TrieRAM<T> {
        match self {
            UncommittedState::RW(ref trie_ram) => trie_ram,
            UncommittedState::Sealed(ref trie_ram, ..) => trie_ram,
        }
    }

    /// Get a mutable reference to the inner TrieRAM
    pub fn trie_ram_mut(&mut self) -> &mut TrieRAM<T> {
        match self {
            UncommittedState::RW(ref mut trie_ram) => trie_ram,
            UncommittedState::Sealed(ref mut trie_ram, ..) => trie_ram,
        }
    }

    /// Read a node's hash
    pub fn read_node_hash(&self, ptr: &TriePtr) -> Result<TrieHash, Error> {
        self.trie_ram_ref().read_node_hash(ptr)
    }

    /// Read a node's hash and the node itself
    pub fn read_nodetype(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        self.trie_ram_mut().read_nodetype(ptr)
    }

    /// Write a node and its hash to a particular slot in the TrieRAM.
    /// Panics of the UncommittedState is sealed already.
    pub fn write_nodetype(
        &mut self,
        node_array_ptr: u32,
        node: &TrieNodeType,
        hash: TrieHash,
    ) -> Result<(), Error> {
        match self {
            UncommittedState::RW(ref mut trie_ram) => {
                trie_ram.write_nodetype(node_array_ptr, node, hash)
            }
            UncommittedState::Sealed(..) => {
                panic!("FATAL: tried to write to a sealed TrieRAM");
            }
        }
    }

    /// Write a node hash to a particular slot in the TrieRAM.
    /// Panics of the UncommittedState is sealed already.
    pub fn write_node_hash(&mut self, node_array_ptr: u32, hash: TrieHash) -> Result<(), Error> {
        match self {
            UncommittedState::RW(ref mut trie_ram) => {
                trie_ram.write_node_hash(node_array_ptr, hash)
            }
            UncommittedState::Sealed(..) => {
                panic!("FATAL: tried to write to a sealed TrieRAM");
            }
        }
    }

    /// Get the last pointer (i.e. last slot) of the TrieRAM
    pub fn last_ptr(&mut self) -> Result<u32, Error> {
        self.trie_ram_mut().last_ptr()
    }

    /// Seal the TrieRAM.  Calculate its root hash and prevent any subsequent writes from
    /// succeeding.
    fn seal(
        self,
        storage_tx: &mut TrieStorageTransaction<T>,
    ) -> Result<UncommittedState<T>, Error> {
        match self {
            UncommittedState::RW(mut trie_ram) => {
                let root_hash = trie_ram.inner_seal(storage_tx)?;
                Ok(UncommittedState::Sealed(trie_ram, root_hash))
            }
            _ => {
                panic!("FATAL: tried to re-seal a sealed TrieRAM");
            }
        }
    }

    /// Dump the TrieRAM to the given writeable `f`.  If the TrieRAM is not sealed yet, then seal
    /// it first and then dump it.
    fn dump<F: Write + Seek>(
        self,
        storage_tx: &mut TrieStorageTransaction<T>,
        f: &mut F,
        bhh: &T,
    ) -> Result<(), Error> {
        if self.trie_ram_ref().block_header != *bhh {
            error!("Failed to dump {:?}: not the current block", bhh);
            return Err(Error::NotFoundError);
        }

        match self {
            UncommittedState::RW(mut trie_ram) => {
                // seal it first, then dump it
                debug!("Seal and dump trie for {}", bhh);
                trie_ram.inner_seal_dump(storage_tx)?;
                trie_ram.dump_consume(f)?;
                Ok(())
            }
            UncommittedState::Sealed(trie_ram, _rh) => {
                // already sealed
                debug!(
                    "Dump already-sealed trie for {} (root hash was {})",
                    bhh, _rh
                );
                trie_ram.dump_consume(f)?;
                Ok(())
            }
        }
    }

    #[cfg(test)]
    pub fn print_to_stderr(&self) {
        self.trie_ram_ref().print_to_stderr()
    }
}

/// In-RAM trie storage.
/// Used by TrieFileStorage to buffer the next trie being built.
#[derive(Clone)]
pub struct TrieRAM<T: MarfTrieId> {
    data: Vec<(TrieNodeType, TrieHash)>,
    block_header: T,
    readonly: bool,

    read_count: u64,
    read_backptr_count: u64,
    read_node_count: u64,
    read_leaf_count: u64,

    write_count: u64,
    write_node_count: u64,
    write_leaf_count: u64,

    total_bytes: usize,

    /// does this TrieRAM represent data temporarily moved out of another TrieRAM?
    is_moved: bool,

    parent: T,
}

/// Trie in RAM without the serialization overhead
impl<T: MarfTrieId> TrieRAM<T> {
    pub fn new(block_header: &T, capacity_hint: usize, parent: &T) -> TrieRAM<T> {
        TrieRAM {
            data: Vec::with_capacity(capacity_hint),
            block_header: block_header.clone(),
            readonly: false,

            read_count: 0,
            read_backptr_count: 0,
            read_node_count: 0,
            read_leaf_count: 0,

            write_count: 0,
            write_node_count: 0,
            write_leaf_count: 0,

            total_bytes: 0,

            is_moved: false,

            parent: parent.clone(),
        }
    }

    /// Inner method to instantiate a TrieRAM from existing Trie data.
    fn from_data(block_header: T, data: Vec<(TrieNodeType, TrieHash)>, parent: T) -> TrieRAM<T> {
        TrieRAM {
            data,
            block_header,
            readonly: false,

            read_count: 0,
            read_backptr_count: 0,
            read_node_count: 0,
            read_leaf_count: 0,

            write_count: 0,
            write_node_count: 0,
            write_leaf_count: 0,

            total_bytes: 0,

            is_moved: false,

            parent,
        }
    }

    /// Instantiate a `TrieRAM` from this `TrieRAM`'s `data` and `block_header`.  This TrieRAM will
    /// have its data set to an empty list.  The new TrieRAM will have its `is_moved` field set to
    /// `true`.
    /// The purpose of this method is to temporarily "re-instate" a `TrieRAM` into a
    /// `TrieFileStorage` while it is being flushed, so that all of the `TrieFileStorage` methods
    /// will continue to work on it.
    ///
    /// Do not call directly; instead, use `with_reinstated_data()`.
    fn move_to(&mut self) -> TrieRAM<T> {
        let moved_data = std::mem::replace(&mut self.data, vec![]);
        TrieRAM {
            data: moved_data,
            block_header: self.block_header.clone(),
            readonly: self.readonly,

            read_count: self.read_count,
            read_backptr_count: self.read_backptr_count,
            read_node_count: self.read_node_count,
            read_leaf_count: self.read_leaf_count,

            write_count: self.write_count,
            write_node_count: self.write_node_count,
            write_leaf_count: self.write_leaf_count,

            total_bytes: self.total_bytes,

            is_moved: true,

            parent: self.parent.clone(),
        }
    }

    /// Take a given `TrieRAM` and move its `data` to this `TrieRAM`'s data.
    /// The given `TrieRAM` *must* have been created with a prior call to `self.move_to()`.
    ///
    /// Do not call directly; instead use `with_reinstated_data()`.
    fn replace_from(&mut self, other: TrieRAM<T>) {
        assert!(!self.is_moved);
        assert!(other.is_moved);
        assert_eq!(self.block_header, other.block_header);
        let _ = std::mem::replace(&mut self.data, other.data);
    }

    /// Temporarily re-instate this TrieRAM's data as the `uncommitted_writes` field in a given storage
    /// connection, run the closure `f` with it, and then restore the original `uncommitted_writes` data.
    /// This method does not compose -- calling `with_reinstated_data` within the given closure `f`
    /// will lead to a runtime panic.
    ///
    /// The purpose of this method is to calculate the trie root hash from a trie that is in the
    /// process of being flushed.
    fn with_reinstated_data<F, R>(&mut self, storage: &mut TrieStorageTransaction<T>, f: F) -> R
    where
        F: FnOnce(&mut TrieRAM<T>, &mut TrieStorageTransaction<T>) -> R,
    {
        // do NOT call this function within another instance of this function.  Only tears and
        // misery would result.
        assert!(
            !self.is_moved,
            "FATAL: tried to move a TrieRAM after it had been moved"
        );

        let old_uncommitted_writes = storage.data.uncommitted_writes.take();

        let moved_trie_ram = self.move_to();
        storage.data.uncommitted_writes = Some((
            self.block_header.clone(),
            UncommittedState::RW(moved_trie_ram),
        ));

        let result = f(self, storage);

        // restore
        let (_, moved_extended) = storage
            .data
            .uncommitted_writes
            .take()
            .expect("FATAL: unable to retake moved TrieRAM");

        match moved_extended {
            UncommittedState::RW(trie_ram) => {
                self.replace_from(trie_ram);
            }
            _ => {
                unreachable!()
            }
        };

        storage.data.uncommitted_writes = old_uncommitted_writes;
        result
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub fn stats(&mut self) -> (u64, u64) {
        let r = self.read_count;
        let w = self.write_count;
        self.read_count = 0;
        self.write_count = 0;
        (r, w)
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub fn node_stats(&mut self) -> (u64, u64, u64) {
        let nr = self.read_node_count;
        let br = self.read_backptr_count;
        let nw = self.write_node_count;

        self.read_node_count = 0;
        self.read_backptr_count = 0;
        self.write_node_count = 0;

        (nr, br, nw)
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub fn leaf_stats(&mut self) -> (u64, u64) {
        let lr = self.read_leaf_count;
        let lw = self.write_leaf_count;

        self.read_leaf_count = 0;
        self.write_leaf_count = 0;

        (lr, lw)
    }

    /// write the trie data to f, using node_data_order to
    ///   iterate over node_data
    pub fn write_trie_indirect<F: Write + Seek>(
        f: &mut F,
        node_data_order: &[u32],
        node_data: &[(TrieNodeType, TrieHash)],
        offsets: &[u32],
        parent_hash: &T,
    ) -> Result<(), Error> {
        assert_eq!(node_data_order.len(), offsets.len());

        // write parent block ptr
        f.seek(SeekFrom::Start(0))?;
        f.write_all(parent_hash.as_bytes())
            .map_err(Error::IOError)?;
        // write zero-identifier (TODO: this is a convenience hack for now, we should remove the
        //    identifier from the trie data blob)
        f.seek(SeekFrom::Start(BLOCK_HEADER_HASH_ENCODED_SIZE as u64))?;
        f.write_all(&0u32.to_le_bytes()).map_err(Error::IOError)?;

        for (ix, indirect) in node_data_order.iter().enumerate() {
            // dump the node to storage
            write_nodetype_bytes(
                f,
                &node_data[*indirect as usize].0,
                node_data[*indirect as usize].1,
            )?;

            // next node
            f.seek(SeekFrom::Start(offsets[ix] as u64))?;
        }

        Ok(())
    }

    /// Calculate the MARF root hash from a trie root hash.
    /// This hashes the trie root hash with a geometric series of prior trie hashes.
    fn calculate_marf_root_hash(
        &mut self,
        storage: &mut TrieStorageTransaction<T>,
        root_hash: &TrieHash,
    ) -> TrieHash {
        let (cur_block_hash, cur_block_id) = storage.get_cur_block_and_id();

        storage.data.set_block(self.block_header.clone(), None);

        let marf_root_hash = Trie::get_trie_root_hash(storage, root_hash)
            .expect("FATAL: unable to calculate MARF root hash from moved TrieRAM");

        test_debug!("cur_block_hash = {}, cur_block_id = {:?}, self.block_header = {}, have last extended? {}, root_hash: {}, trie_root_hash = {}", &cur_block_hash, &cur_block_id, &self.block_header, storage.data.uncommitted_writes.is_some(), root_hash, &marf_root_hash);

        storage.data.set_block(cur_block_hash, cur_block_id);

        marf_root_hash
    }

    /// Calculate and store the MARF root hash, as well as any necessary intermediate nodes.  Do
    /// this only for deferred hashing mode.
    fn inner_seal_marf(
        &mut self,
        storage_tx: &mut TrieStorageTransaction<T>,
    ) -> Result<TrieHash, Error> {
        // find trie root hash
        debug!("Calculate trie root hash");
        let root_trie_hash = self.calculate_node_hashes(storage_tx, 0)?;

        // find marf root hash -- the hash of the trie root node hash, and the hashes of the
        // geometric series of ancestor tries.  Because the trie is already in the process of
        // being flushed, we have to temporarily reinstate its data into `storage_tx` so we can
        // use it to walk down the various MARF paths needed to query ancestor tries.
        let marf_root_hash = self.with_reinstated_data(storage_tx, |moved_trieram, storage| {
            debug!("Calculate marf root hash");
            moved_trieram.calculate_marf_root_hash(storage, &root_trie_hash)
        });

        if TrieHashCalculationMode::All == storage_tx.deref().hash_calculation_mode {
            // If we are doing both eager and deferred hashing (i.e. via a test), then verify
            // that we get the same marf hash either way.
            let (_, expected_root_hash) = self.get_nodetype(0)?;
            assert_eq!(expected_root_hash, &marf_root_hash);
        }

        // need to store this hash too, since we deferred calculation
        self.write_node_hash(0, marf_root_hash.clone())?;
        Ok(marf_root_hash)
    }

    /// Get the trie root hash of the trie ram, and update all nodes' root hashes if we're in
    /// deferred hash mode.  Returns the resulting MARF root.  This is part of the seal operation.
    fn inner_seal(
        &mut self,
        storage_tx: &mut TrieStorageTransaction<T>,
    ) -> Result<TrieHash, Error> {
        if TrieHashCalculationMode::Deferred == storage_tx.deref().hash_calculation_mode
            || TrieHashCalculationMode::All == storage_tx.deref().hash_calculation_mode
        {
            self.inner_seal_marf(storage_tx)
        } else {
            // already available
            let marf_root_hash =
                self.read_node_hash(&TriePtr::new(TrieNodeID::Node256 as u8, 0, 0))?;
            Ok(marf_root_hash)
        }
    }

    #[cfg(test)]
    pub fn test_inner_seal(
        &mut self,
        storage_tx: &mut TrieStorageTransaction<T>,
    ) -> Result<TrieHash, Error> {
        self.inner_seal(storage_tx)
    }

    /// Seal a trie ram while in the process of dumping it.  If the storage's hash calculation mode
    /// is Deferred, then this updates all the node hashes as well and stores the new node hash.
    /// Otherwise, this is a no-op.
    /// This part of the seal operation.
    fn inner_seal_dump(&mut self, storage_tx: &mut TrieStorageTransaction<T>) -> Result<(), Error> {
        if TrieHashCalculationMode::Deferred == storage_tx.deref().hash_calculation_mode
            || TrieHashCalculationMode::All == storage_tx.deref().hash_calculation_mode
        {
            let marf_root_hash = self.inner_seal_marf(storage_tx)?;
            debug!("Deferred root hash calculation is {}", &marf_root_hash);
        }
        Ok(())
    }

    /// Recursively calculate all node hashes in this `TrieRAM`.  The top-most call to this method
    /// should pass `0` for `node_ptr`, since this is the pointer to the root node.  Returns the
    /// node hash for the `TrieNode` at `node_ptr`.
    /// If the given `storage_tx`'s hash calculation mode is set to
    /// `TrieHashCalculationMode::Deferred`, then this method will also store each non-leaf node's
    /// hash.
    fn calculate_node_hashes(
        &mut self,
        storage_tx: &mut TrieStorageTransaction<T>,
        node_ptr: u64,
    ) -> Result<TrieHash, Error> {
        let start_time = storage_tx.bench.write_children_hashes_start();
        let mut start_node_time = Some(storage_tx.bench.write_children_hashes_same_block_start());
        let (node, node_hash) = self.get_nodetype(node_ptr as u32)?.to_owned();
        if node.is_leaf() {
            // base case: we already have the hash of the leaf, so return it.
            Ok(node_hash)
        } else {
            // inductive case: calculate children hashes, hash them, and return that hash.
            let mut hasher = TrieHasher::new();
            let empty_node_hash = TrieHash::from_data(&[]);

            node.write_consensus_bytes(storage_tx, &mut hasher)
                .expect("IO Failure pushing to hasher.");

            // count get_nodetype load time for write_children_hashes_same_block benchmark, but
            // only if that code path will be exercised.
            for ptr in node.ptrs().iter() {
                if !is_backptr(ptr.id()) && ptr.id() != TrieNodeID::Empty as u8 {
                    if let Some(start_node_time) = start_node_time.take() {
                        // count the time taken to load the root node in this case,
                        // but only do so once.
                        storage_tx
                            .bench
                            .write_children_hashes_same_block_finish(start_node_time);
                        break;
                    }
                }
            }

            // calculate the hashes of this node's children, and store them if they're in the
            // same trie.
            for ptr in node.ptrs().iter() {
                if ptr.id() == TrieNodeID::Empty as u8 {
                    // hash of empty string
                    let start_time = storage_tx.bench.write_children_hashes_empty_start();

                    hasher.write_all(empty_node_hash.as_bytes())?;

                    storage_tx
                        .bench
                        .write_children_hashes_empty_finish(start_time);
                } else if !is_backptr(ptr.id()) {
                    // hash is the hash of this node's children
                    let node_hash = self.calculate_node_hashes(storage_tx, ptr.ptr() as u64)?;

                    // count the time taken to store the hash towards the
                    // write_children_hashes_same_benchmark
                    let start_time = storage_tx.bench.write_children_hashes_same_block_start();
                    trace!(
                        "calculate_node_hashes({:?}): at chr {} ptr {}: {:?} {:?}",
                        &self.block_header,
                        ptr.chr(),
                        ptr.ptr(),
                        &node_hash,
                        node
                    );
                    hasher.write_all(node_hash.as_bytes())?;

                    if TrieHashCalculationMode::Deferred == storage_tx.deref().hash_calculation_mode
                        && ptr.id() != TrieNodeID::Leaf as u8
                    {
                        // need to store this hash too, since we deferred calculation
                        self.write_node_hash(ptr.ptr(), node_hash)?;
                    }

                    storage_tx
                        .bench
                        .write_children_hashes_same_block_finish(start_time);
                } else {
                    // hash is that of the block that contains this node
                    let start_time = storage_tx
                        .bench
                        .write_children_hashes_ancestor_block_start();

                    let block_hash = storage_tx.get_block_hash_caching(ptr.back_block())?;
                    trace!(
                        "calculate_node_hashes({:?}): at chr {} bkptr {}: {:?} {:?}",
                        &self.block_header,
                        ptr.chr(),
                        ptr.ptr(),
                        &block_hash,
                        node
                    );
                    hasher.write_all(block_hash.as_bytes())?;

                    storage_tx
                        .bench
                        .write_children_hashes_ancestor_block_finish(start_time);
                }
            }

            // only measure full trie
            if node_ptr == 0 {
                storage_tx
                    .bench
                    .write_children_hashes_finish(start_time, true);
            }

            let node_hash = {
                let mut buf = [0u8; 32];
                buf.copy_from_slice(hasher.finalize().as_slice());
                TrieHash(buf)
            };

            Ok(node_hash)
        }
    }

    /// Walk through the buffered TrieNodes and dump them to f.
    /// This consumes this TrieRAM instance.
    fn dump_consume<F: Write + Seek>(mut self, f: &mut F) -> Result<u64, Error> {
        // step 1: write out each node in breadth-first order to get their ptr offsets
        let mut frontier: VecDeque<u32> = VecDeque::new();

        let mut node_data = vec![];
        let mut offsets = vec![];

        let start = TriePtr::new(TrieNodeID::Node256 as u8, 0, 0).ptr();
        frontier.push_back(start);

        // first 32 bytes is reserved for the parent block hash
        //    next 4 bytes is the local block identifier
        let mut ptr = BLOCK_HEADER_HASH_ENCODED_SIZE as u64 + 4;

        while let Some(pointer) = frontier.pop_front() {
            let (node, _node_hash) = self.get_nodetype(pointer)?;
            // calculate size
            let num_written = get_node_byte_len(node);
            ptr += num_written as u64;

            // queue each child
            if !node.is_leaf() {
                let ptrs = node.ptrs();
                let num_children = ptrs.len();
                for i in 0..num_children {
                    if ptrs[i].id != TrieNodeID::Empty as u8 && !is_backptr(ptrs[i].id) {
                        frontier.push_back(ptrs[i].ptr());
                    }
                }
            }

            node_data.push(pointer);
            offsets.push(ptr as u32);
        }

        assert_eq!(offsets.len(), node_data.len());

        // step 2: update ptrs in all nodes
        let mut i = 0;
        for j in 0..node_data.len() {
            let next_node = &mut self.data[node_data[j] as usize].0;
            if !next_node.is_leaf() {
                let ptrs = next_node.ptrs_mut();
                let num_children = ptrs.len();
                for k in 0..num_children {
                    if ptrs[k].id != TrieNodeID::Empty as u8 && !is_backptr(ptrs[k].id) {
                        ptrs[k].ptr = offsets[i];
                        i += 1;
                    }
                }
            }
        }

        // step 3: write out each node (now that they have the write ptrs)
        TrieRAM::write_trie_indirect(
            f,
            &node_data,
            self.data.as_slice(),
            offsets.as_slice(),
            &self.parent,
        )?;

        Ok(ptr)
    }

    /// load the trie from F.
    /// The trie will have the same structure as the on-disk trie, but it may have nodes in a
    /// different order.
    pub fn load<F: Read + Seek>(f: &mut F, bhh: &T) -> Result<TrieRAM<T>, Error> {
        let mut data = vec![];
        let mut frontier = VecDeque::new();

        // read parent
        f.seek(SeekFrom::Start(0))?;
        let parent_hash_bytes = read_hash_bytes(f)?;
        let parent_hash = T::from_bytes(parent_hash_bytes);

        let root_disk_ptr = BLOCK_HEADER_HASH_ENCODED_SIZE as u64 + 4;

        let root_ptr = TriePtr::new(TrieNodeID::Node256 as u8, 0, root_disk_ptr as u32);
        let (mut root_node, root_hash) = read_nodetype(f, &root_ptr)
            .inspect_err(|e| error!("Failed to read root node info for {bhh:?}: {e:?}"))?;

        let mut next_index = 1;

        if let TrieNodeType::Node256(ref mut data) = root_node {
            // queue children in the same order we stored them
            for ptr in data.ptrs.iter_mut() {
                if ptr.id() != TrieNodeID::Empty as u8 && !is_backptr(ptr.id()) {
                    frontier.push_back((*ptr).clone());

                    // fix up ptrs
                    ptr.ptr = next_index;
                    next_index += 1;
                }
            }
        } else {
            return Err(Error::CorruptionError(
                "First TrieRAM node is not a Node256".to_string(),
            ));
        }

        data.push((root_node, root_hash));

        while !frontier.is_empty() {
            let next_ptr = frontier
                .pop_front()
                .expect("BUG: no ptr in non-empty frontier");
            let (mut next_node, next_hash) = read_nodetype(f, &next_ptr)
                .inspect_err(|e| error!("Failed to read node at {next_ptr:?}: {e:?}"))?;

            if !next_node.is_leaf() {
                // queue children in the same order we stored them
                let ptrs: &mut [TriePtr] = match next_node {
                    TrieNodeType::Node4(ref mut data) => &mut data.ptrs,
                    TrieNodeType::Node16(ref mut data) => &mut data.ptrs,
                    TrieNodeType::Node48(ref mut data) => &mut data.ptrs,
                    TrieNodeType::Node256(ref mut data) => &mut data.ptrs,
                    _ => {
                        unreachable!();
                    }
                };

                for ptr in ptrs {
                    if ptr.id() != TrieNodeID::Empty as u8 && !is_backptr(ptr.id()) {
                        frontier.push_back((*ptr).clone());

                        // fix up ptrs
                        ptr.ptr = next_index;
                        next_index += 1;
                    }
                }
            }

            data.push((next_node, next_hash));
        }

        Ok(TrieRAM::from_data((*bhh).clone(), data, parent_hash))
    }

    /// Hint as to how many entries to allocate for the inner Vec when creating a TrieRAM
    fn size_hint(&self) -> usize {
        self.write_count as usize
        // the size hint is used for a capacity guess on the data vec, which is _nodes_
        //  NOT bytes. this led to enormous over-allocations
    }

    /// Clear the TrieRAM contents
    pub fn format(&mut self) -> Result<(), Error> {
        if self.readonly {
            trace!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        self.data.clear();
        Ok(())
    }

    /// Read a node's hash from the TrieRAM.  ptr.ptr() is an array index.
    pub fn read_node_hash(&self, ptr: &TriePtr) -> Result<TrieHash, Error> {
        let (_, node_trie_hash) = self.data.get(ptr.ptr() as usize).ok_or_else(|| {
            error!(
                "TrieRAM: Failed to read node bytes: {} >= {}",
                ptr.ptr(),
                self.data.len()
            );
            Error::NotFoundError
        })?;

        Ok(node_trie_hash.clone())
    }

    /// Get an immutable reference to a node and its hash from the TrieRAM.  ptr.ptr() is an array index.
    pub fn get_nodetype(&self, ptr: u32) -> Result<&(TrieNodeType, TrieHash), Error> {
        self.data.get(ptr as usize).ok_or_else(|| {
            error!(
                "TrieRAM get_nodetype({:?}): Failed to read node: {} >= {}",
                &self.block_header,
                ptr,
                self.data.len()
            );
            Error::NotFoundError
        })
    }

    /// Get an owned instance of a node and its hash from the TrieRAM.  ptr.ptr() is an array
    /// index.
    pub fn read_nodetype(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        trace!(
            "TrieRAM: read_nodetype({:?}): at {:?}",
            &self.block_header,
            ptr
        );

        self.read_count += 1;
        if is_backptr(ptr.id()) {
            self.read_backptr_count += 1;
        } else if ptr.id() == TrieNodeID::Leaf as u8 {
            self.read_leaf_count += 1;
        } else {
            self.read_node_count += 1;
        }

        if (ptr.ptr() as u64) >= (self.data.len() as u64) {
            error!(
                "TrieRAM read_nodetype({:?}): Failed to read node {:?}: {} >= {}",
                &self.block_header,
                ptr,
                ptr.ptr(),
                self.data.len()
            );
            Err(Error::NotFoundError)
        } else {
            Ok(self.data[ptr.ptr() as usize].clone())
        }
    }

    /// Store a node and its hash to the TrieRAM at the given slot.
    pub fn write_nodetype(
        &mut self,
        node_array_ptr: u32,
        node: &TrieNodeType,
        hash: TrieHash,
    ) -> Result<(), Error> {
        if self.readonly {
            trace!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        trace!(
            "TrieRAM: write_nodetype({:?}): at {node_array_ptr}: {hash:?} {node:?}",
            &self.block_header,
        );

        self.write_count += 1;
        match node {
            TrieNodeType::Leaf(_) => {
                self.write_leaf_count += 1;
            }
            _ => {
                self.write_node_count += 1;
            }
        }

        let node_array_ptr = usize::try_from(node_array_ptr).map_err(|e| {
            error!("Conversion to usize failed: {e}");
            Error::NotFoundError
        })?;
        match node_array_ptr.cmp(&self.data.len()) {
            Ordering::Less => {
                self.data[node_array_ptr] = (node.clone(), hash);
                Ok(())
            }
            Ordering::Equal => {
                self.data.push((node.clone(), hash));
                self.total_bytes += get_node_byte_len(node);
                Ok(())
            }
            Ordering::Greater => {
                error!("Failed to write node bytes: off the end of the buffer");
                Err(Error::NotFoundError)
            }
        }
    }

    /// Store a node hash into the TrieRAM at a given node slot.
    pub fn write_node_hash(&mut self, node_array_ptr: u32, hash: TrieHash) -> Result<(), Error> {
        if self.readonly {
            trace!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        trace!(
            "TrieRAM: write_node_hash({:?}): at {}: {:?}",
            &self.block_header,
            node_array_ptr,
            &hash,
        );

        // can only set the hash of an existing node
        if node_array_ptr < (self.data.len() as u32) {
            self.data[node_array_ptr as usize].1 = hash;
            Ok(())
        } else {
            error!("Failed to write node hash bytes: off the end of the buffer");
            Err(Error::NotFoundError)
        }
    }

    /// Get the next ptr value for a node to store.
    pub fn last_ptr(&mut self) -> Result<u32, Error> {
        Ok(self.data.len() as u32)
    }

    #[cfg(test)]
    pub fn print_to_stderr(&self) {
        for dat in self.data.iter() {
            eprintln!("{}: {:?}", &dat.1, &dat.0);
        }
    }

    #[cfg(test)]
    pub fn data(&self) -> &Vec<(TrieNodeType, TrieHash)> {
        &self.data
    }
}

impl<T: MarfTrieId> NodeHashReader for TrieRAM<T> {
    fn read_node_hash_bytes<W: Write>(&mut self, ptr: &TriePtr, w: &mut W) -> Result<(), Error> {
        let (_, node_trie_hash) = self.data.get(ptr.ptr() as usize).ok_or_else(|| {
            error!(
                "TrieRAM: Failed to read node bytes: {} >= {}",
                ptr.ptr(),
                self.data.len()
            );
            Error::NotFoundError
        })?;
        w.write_all(node_trie_hash.as_bytes())?;
        Ok(())
    }
}

pub struct TrieSqlCursor<'a> {
    db: &'a Connection,
    block_id: u32,
}

pub struct TrieSqlHashMapCursor<'a, T: MarfTrieId> {
    db: &'a Connection,
    cache: &'a mut TrieCache<T>,
    unconfirmed: bool,
}

impl NodeHashReader for TrieSqlCursor<'_> {
    fn read_node_hash_bytes<W: Write>(&mut self, ptr: &TriePtr, w: &mut W) -> Result<(), Error> {
        trie_sql::read_node_hash_bytes(self.db, w, self.block_id, ptr)
    }
}

enum SqliteConnection<'a> {
    ConnRef(&'a Connection),
    Tx(Transaction<'a>),
}

impl Deref for SqliteConnection<'_> {
    type Target = Connection;
    fn deref(&self) -> &Connection {
        match self {
            SqliteConnection::ConnRef(x) => x,
            SqliteConnection::Tx(tx) => tx,
        }
    }
}

impl<'a, T: MarfTrieId> Deref for TrieStorageTransaction<'a, T> {
    type Target = TrieStorageConnection<'a, T>;
    fn deref(&self) -> &TrieStorageConnection<'a, T> {
        &self.0
    }
}

impl<'a, T: MarfTrieId> DerefMut for TrieStorageTransaction<'a, T> {
    fn deref_mut(&mut self) -> &mut TrieStorageConnection<'a, T> {
        &mut self.0
    }
}

///
/// TrieStorageTransaction is a pointer to an open TrieFileStorage with an
///   open SQLite transaction. Any storage methods which require a transaction
///   are defined _only_ for this struct (e.g., the flush methods).
///
pub struct TrieStorageTransaction<'a, T: MarfTrieId>(TrieStorageConnection<'a, T>);

/// Hash calculation mode
#[derive(Debug, Clone, PartialEq, Copy)]
pub enum TrieHashCalculationMode {
    /// Calculate all trie node hashes as we insert leaves
    Immediate,
    /// Do not calculate trie node hashes until we dump the trie to disk
    Deferred,
    /// Calculate trie hashes both on leaf insert and on trie dump.  Used for testing.
    All,
}

///
///  TrieStorageConnection is a pointer to an open TrieFileStorage,
///    with either a SQLite &Connection (non-mut, so it cannot start a TX)
///    or a Transaction. Mutations on TrieStorageConnection's `data` field
///    propagate to the TrieFileStorage that created the connection.
///  This is the main interface to the storage methods, and defines most
///    of the storage functionality.
///
pub struct TrieStorageConnection<'a, T: MarfTrieId> {
    pub db_path: &'a str,
    db: SqliteConnection<'a>,
    blobs: Option<&'a mut TrieFile>,
    data: &'a mut TrieStorageTransientData<T>,
    cache: &'a mut TrieCache<T>,
    bench: &'a mut TrieBenchmark,
    pub hash_calculation_mode: TrieHashCalculationMode,

    /// row ID of a trie that represents unconfirmed state (i.e. trie state that will never become
    /// part of the MARF, but nevertheless represents a persistent scratch space).  If this field
    /// is Some(..), then the storage connection here was used to (re-)open an unconfirmed trie
    /// (via `open_unconfirmed()` or `open_block()` when `self.unconfirmed()` is `true`), or used
    /// to create an unconfirmed trie (via `extend_to_unconfirmed_block()`).
    unconfirmed_block_id: Option<u32>,

    // used in testing in order to short-circuit block-height lookups
    //   when the trie struct is tested outside of marf.rs usage
    #[cfg(test)]
    pub test_genesis_block: &'a mut Option<T>,
}

///
///  TrieStorageTransientData holds all the data that _isn't_ committed
///   to the underlying SQL storage. Used internally to simplify
///   the TrieStorageConnection/TrieFileStorage interactions
///
pub struct TrieStorageTransientData<T: MarfTrieId> {
    /// This is all the nodes written but not yet committed to disk.
    pub uncommitted_writes: Option<(T, UncommittedState<T>)>,

    /// Currently-open block (may be `uncommitted_writes.unwrap().0`)
    cur_block: T,
    /// Tracking the row_id for the cur_block. If cur_block == uncommitted_writes,
    ///   this value should always be None
    cur_block_id: Option<u32>,

    /// Runtime statistics on reading nodes
    read_count: u64,
    read_backptr_count: u64,
    read_node_count: u64,
    read_leaf_count: u64,

    /// Runtime statistics on writing nodes
    write_count: u64,
    write_node_count: u64,
    write_leaf_count: u64,

    /// List of ancestral trie root hashes that must be hashed with the `uncommitted_writes` root node
    /// hash to produce the MarfTrieId for the trie when it gets written to disk.  This is
    /// maintained by the MARF whenever it needs to update the trie root hash after a leaf insert,
    /// so that a batch of leaf inserts into `uncommitted_writes` don't require an ancestor trie hash
    /// query more than once.
    trie_ancestor_hash_bytes_cache: Option<(T, Vec<TrieHash>)>,

    /// Is the trie opened read-only?
    readonly: bool,

    /// Does this trie represent unconfirmed state?
    unconfirmed: bool,
}

// disk-backed Trie.
// Keeps the last-extended Trie in-RAM and flushes it to disk on either a call to flush() or a call
// to extend_to_block() with a different block header hash.
pub struct TrieFileStorage<T: MarfTrieId> {
    pub db_path: String,

    db: Connection,
    blobs: Option<TrieFile>,
    data: TrieStorageTransientData<T>,
    cache: TrieCache<T>,
    bench: TrieBenchmark,
    hash_calculation_mode: TrieHashCalculationMode,

    // used in testing in order to short-circuit block-height lookups
    //   when the trie struct is tested outside of marf.rs usage
    #[cfg(test)]
    pub test_genesis_block: Option<T>,
}

/// Helper to open a MARF
fn marf_sqlite_open<P: AsRef<Path>>(
    db_path: P,
    open_flags: OpenFlags,
    foreign_keys: bool,
) -> Result<Connection, db_error> {
    let db = sqlite_open(db_path, open_flags, foreign_keys)?;
    sql_pragma(&db, "mmap_size", &SQLITE_MMAP_SIZE)?;
    sql_pragma(&db, "page_size", &SQLITE_MARF_PAGE_SIZE)?;
    Ok(db)
}

impl<T: MarfTrieId> TrieStorageTransientData<T> {
    /// Target the transient data to a particular block, and optionally its block ID
    fn set_block(&mut self, bhh: T, id: Option<u32>) {
        trace!("set_block({},{:?})", &bhh, &id);
        self.cur_block_id = id;
        self.cur_block = bhh;
    }

    fn clear_block_id(&mut self) {
        self.cur_block_id = None;
    }

    fn retarget_block(&mut self, bhh: T) {
        self.cur_block = bhh;
    }
}

impl<T: MarfTrieId> TrieFileStorage<T> {
    pub fn connection(&mut self) -> TrieStorageConnection<'_, T> {
        TrieStorageConnection {
            db: SqliteConnection::ConnRef(&self.db),
            db_path: &self.db_path,
            data: &mut self.data,
            blobs: self.blobs.as_mut(),
            cache: &mut self.cache,
            bench: &mut self.bench,
            hash_calculation_mode: self.hash_calculation_mode,
            unconfirmed_block_id: None,

            #[cfg(test)]
            test_genesis_block: &mut self.test_genesis_block,
        }
    }

    pub fn transaction(&mut self) -> Result<TrieStorageTransaction<'_, T>, Error> {
        if self.readonly() {
            return Err(Error::ReadOnlyError);
        }
        let tx = tx_begin_immediate(&mut self.db)?;

        Ok(TrieStorageTransaction(TrieStorageConnection {
            db: SqliteConnection::Tx(tx),
            db_path: &self.db_path,
            data: &mut self.data,
            blobs: self.blobs.as_mut(),
            cache: &mut self.cache,
            bench: &mut self.bench,
            hash_calculation_mode: self.hash_calculation_mode,
            unconfirmed_block_id: None,

            #[cfg(test)]
            test_genesis_block: &mut self.test_genesis_block,
        }))
    }

    pub fn sqlite_conn(&self) -> &Connection {
        &self.db
    }

    pub fn sqlite_tx(&mut self) -> Result<Transaction<'_>, db_error> {
        tx_begin_immediate(&mut self.db)
    }

    pub fn into_sqlite_conn(self) -> Connection {
        self.db
    }

    fn open_opts(
        db_path: &str,
        readonly: bool,
        unconfirmed: bool,
        marf_opts: MARFOpenOpts,
    ) -> Result<TrieFileStorage<T>, Error> {
        let mut create_flag = false;
        let open_flags = if db_path != ":memory:" {
            match fs::metadata(db_path) {
                Err(e) => {
                    if e.kind() == io::ErrorKind::NotFound {
                        // need to create
                        if !readonly {
                            create_flag = true;
                            OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
                        } else {
                            return Err(Error::NotFoundError);
                        }
                    } else {
                        return Err(Error::IOError(e));
                    }
                }
                Ok(_md) => {
                    // can just open
                    if !readonly {
                        OpenFlags::SQLITE_OPEN_READ_WRITE
                    } else {
                        OpenFlags::SQLITE_OPEN_READ_ONLY
                    }
                }
            }
        } else {
            create_flag = true;
            if !readonly {
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
            } else {
                OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_CREATE
            }
        };

        let mut db = marf_sqlite_open(db_path, open_flags, false)?;
        let db_path = db_path.to_string();

        if create_flag {
            trie_sql::create_tables_if_needed(&mut db)?;
        }

        let mut blobs = if marf_opts.external_blobs {
            Some(TrieFile::from_db_path(&db_path, readonly)?)
        } else {
            None
        };

        let prev_schema_version = trie_sql::migrate_tables_if_needed::<T>(&mut db)?;
        if prev_schema_version != trie_sql::SQL_MARF_SCHEMA_VERSION || marf_opts.force_db_migrate {
            if let Some(blobs) = blobs.as_mut() {
                if TrieFile::exists(&db_path)? {
                    // migrate blobs out of the old DB
                    blobs.export_trie_blobs::<T>(&db, &db_path)?;
                }
            }
        }
        if trie_sql::detect_partial_migration(&db)? {
            panic!("PARTIAL MIGRATION DETECTED! This is an irrecoverable error. You will need to restart your node from genesis.");
        }

        debug!(
            "Opened TrieFileStorage {}; external blobs: {}",
            db_path,
            blobs.is_some()
        );

        let cache = TrieCache::new(&marf_opts.cache_strategy);

        let ret = TrieFileStorage {
            db_path,
            db,
            cache,
            blobs,
            bench: TrieBenchmark::new(),
            hash_calculation_mode: marf_opts.hash_calculation_mode,

            data: TrieStorageTransientData {
                uncommitted_writes: None,
                cur_block: T::sentinel(),
                cur_block_id: None,

                read_count: 0,
                read_backptr_count: 0,
                read_node_count: 0,
                read_leaf_count: 0,

                write_count: 0,
                write_node_count: 0,
                write_leaf_count: 0,

                trie_ancestor_hash_bytes_cache: None,

                readonly,
                unconfirmed,
            },

            // used in testing in order to short-circuit block-height lookups
            //   when the trie struct is tested outside of marf.rs usage
            #[cfg(test)]
            test_genesis_block: None,
        };

        Ok(ret)
    }

    #[cfg(test)]
    pub fn new_memory(marf_opts: MARFOpenOpts) -> Result<TrieFileStorage<T>, Error> {
        TrieFileStorage::open(":memory:", marf_opts)
    }

    pub fn open(db_path: &str, marf_opts: MARFOpenOpts) -> Result<TrieFileStorage<T>, Error> {
        TrieFileStorage::open_opts(db_path, false, false, marf_opts)
    }

    pub fn open_readonly(
        db_path: &str,
        marf_opts: MARFOpenOpts,
    ) -> Result<TrieFileStorage<T>, Error> {
        TrieFileStorage::open_opts(db_path, true, false, marf_opts)
    }

    pub fn open_unconfirmed(
        db_path: &str,
        mut marf_opts: MARFOpenOpts,
    ) -> Result<TrieFileStorage<T>, Error> {
        // no caching allowed for unconfirmed tries, since they can disappear
        marf_opts.cache_strategy = "noop".to_string();
        TrieFileStorage::open_opts(db_path, false, true, marf_opts)
    }

    pub fn readonly(&self) -> bool {
        self.data.readonly
    }

    /// Return true if this storage connection was opened with the intention of operating on an
    /// unconfirmed trie -- i.e. this is a storage connection for reading and writing a persisted
    /// scratch space trie, such as one for storing unconfirmed microblock transactions in the
    /// chain state.
    pub fn unconfirmed(&self) -> bool {
        self.data.unconfirmed
    }

    /// Returns a new TrieFileStorage in read-only mode.
    ///
    /// Returns Err if the underlying SQLite database connection cannot be created.
    pub fn reopen_readonly(&self) -> Result<TrieFileStorage<T>, Error> {
        let db = marf_sqlite_open(&self.db_path, OpenFlags::SQLITE_OPEN_READ_ONLY, false)?;
        let cache = TrieCache::default();
        let blobs = if self.blobs.is_some() {
            Some(TrieFile::from_db_path(&self.db_path, true)?)
        } else {
            None
        };

        trace!("Make read-only view of TrieFileStorage: {}", &self.db_path);

        // TODO: borrow self.uncommitted_writes; don't copy them
        let ret = TrieFileStorage {
            db_path: self.db_path.clone(),
            db,
            blobs,
            cache,
            bench: TrieBenchmark::new(),
            hash_calculation_mode: self.hash_calculation_mode,

            data: TrieStorageTransientData {
                uncommitted_writes: self.data.uncommitted_writes.clone(),
                cur_block: self.data.cur_block.clone(),
                cur_block_id: self.data.cur_block_id.clone(),

                read_count: 0,
                read_backptr_count: 0,
                read_node_count: 0,
                read_leaf_count: 0,

                write_count: 0,
                write_node_count: 0,
                write_leaf_count: 0,

                trie_ancestor_hash_bytes_cache: None,

                readonly: true,
                unconfirmed: self.unconfirmed(),
            },

            // used in testing in order to short-circuit block-height lookups
            //   when the trie struct is tested outside of marf.rs usage
            #[cfg(test)]
            test_genesis_block: self.test_genesis_block.clone(),
        };

        Ok(ret)
    }

    pub fn get_benchmarks(&self) -> TrieBenchmark {
        self.bench.clone()
    }

    pub fn bench_mut(&mut self) -> &mut TrieBenchmark {
        &mut self.bench
    }

    pub fn reset_benchmarks(&mut self) {
        self.bench.reset();
    }
}

impl<'a, T: MarfTrieId> TrieStorageTransaction<'a, T> {
    /// reopen this transaction as a read-only marf.
    ///  _does not_ preserve the cur_block/open tip
    pub fn reopen_readonly(&self) -> Result<TrieFileStorage<T>, Error> {
        let db = marf_sqlite_open(&self.db_path, OpenFlags::SQLITE_OPEN_READ_ONLY, false)?;
        let blobs = if self.blobs.is_some() {
            Some(TrieFile::from_db_path(self.db_path, true)?)
        } else {
            None
        };

        trace!(
            "Make read-only view of TrieStorageTransaction: {}",
            &self.db_path
        );

        let cache = TrieCache::default();

        // TODO: borrow self.uncommitted_writes; don't copy them
        let ret = TrieFileStorage {
            db_path: self.db_path.to_string(),
            db,
            blobs,
            cache,
            bench: TrieBenchmark::new(),
            hash_calculation_mode: self.hash_calculation_mode,

            data: TrieStorageTransientData {
                uncommitted_writes: None,
                cur_block: T::sentinel(),
                cur_block_id: None,

                read_count: 0,
                read_backptr_count: 0,
                read_node_count: 0,
                read_leaf_count: 0,

                write_count: 0,
                write_node_count: 0,
                write_leaf_count: 0,

                trie_ancestor_hash_bytes_cache: None,

                readonly: true,
                unconfirmed: self.unconfirmed(),
            },

            // used in testing in order to short-circuit block-height lookups
            //   when the trie struct is tested outside of marf.rs usage
            #[cfg(test)]
            test_genesis_block: self.test_genesis_block.clone(),
        };

        Ok(ret)
    }

    /// Run `cls` with a mutable reference to the inner trie blobs opt.
    fn with_trie_blobs<F, R>(&mut self, cls: F) -> R
    where
        F: FnOnce(&Connection, &mut Option<&mut TrieFile>) -> R,
    {
        let mut blobs = self.blobs.take();
        let res = cls(&self.db, &mut blobs);
        self.blobs = blobs;
        res
    }

    /// Inner method for flushing the UncommittedState's TrieRAM to disk.
    fn inner_flush(&mut self, flush_options: FlushOptions<'_, T>) -> Result<(), Error> {
        // save the currently-buffered Trie to disk, and atomically put it into place (possibly to
        // a different block than the one opened, as indicated by final_bhh).
        // Runs once -- subsequent calls are no-ops.
        // Panics on a failure to rename the Trie file into place (i.e. if the actual commitment
        // fails).
        self.clear_cached_ancestor_hashes_bytes();
        if self.data.readonly {
            return Err(Error::ReadOnlyError);
        }
        if let Some((bhh, trie_ram)) = self.data.uncommitted_writes.take() {
            trace!("Buffering block flush started.");
            let mut buffer = Cursor::new(Vec::new());
            trie_ram.dump(self, &mut buffer, &bhh)?;

            // consume the cursor, get the buffer
            let buffer = buffer.into_inner();
            trace!("Buffering block flush finished.");

            debug!("Flush: {} to {}", &bhh, flush_options);

            let block_id = match flush_options {
                FlushOptions::CurrentHeader => {
                    if self.unconfirmed() {
                        return Err(Error::UnconfirmedError);
                    }
                    self.with_trie_blobs(|db, blobs| match blobs {
                        Some(blobs) => blobs.store_trie_blob(db, &bhh, &buffer),
                        None => {
                            test_debug!("Stored trie blob {bhh} to db");
                            trie_sql::write_trie_blob(db, &bhh, &buffer)
                        }
                    })?
                }
                FlushOptions::NewHeader(real_bhh) => {
                    // If we opened a block with a given hash, but want to store it as a block with a *different*
                    // hash, then call this method to update the internal storage state to make it so.  This is
                    // necessary for validating blocks in the blockchain, since the miner will always build a
                    // block whose hash is all 0's (since it can't know the final block hash).  As such, a peer
                    // will process a block as if it's hash is all 0's (in order to validate the state root), and
                    // then use this method to switch over the block hash to the "real" block hash.
                    if self.data.unconfirmed {
                        return Err(Error::UnconfirmedError);
                    }
                    if real_bhh != &bhh {
                        // note: this was moved from the block_retarget function
                        //  to avoid stepping on the borrow checker.
                        debug!("Retarget block {} to {}", bhh, real_bhh);
                        // switch over state
                        self.data.retarget_block(real_bhh.clone());
                    }
                    self.with_trie_blobs(|db, blobs| match blobs {
                        Some(blobs) => blobs.store_trie_blob(db, real_bhh, &buffer),
                        None => {
                            test_debug!("Stored trie blob {} to db", real_bhh);
                            trie_sql::write_trie_blob(db, real_bhh, &buffer)
                        }
                    })?
                }
                FlushOptions::MinedTable(real_bhh) => {
                    if self.unconfirmed() {
                        return Err(Error::UnconfirmedError);
                    }
                    trie_sql::write_trie_blob_to_mined(&self.db, real_bhh, &buffer)?
                }
                FlushOptions::UnconfirmedTable => {
                    if !self.unconfirmed() {
                        return Err(Error::UnconfirmedError);
                    }
                    trie_sql::write_trie_blob_to_unconfirmed(&self.db, &bhh, &buffer)?
                }
            };

            trie_sql::drop_lock(&self.db, &bhh)?;

            debug!("Flush: identifier of {} is {}", flush_options, block_id);
        }

        Ok(())
    }

    /// Flush uncommitted state to disk.
    pub fn flush(&mut self) -> Result<(), Error> {
        if self.data.unconfirmed {
            self.inner_flush(FlushOptions::UnconfirmedTable)
        } else {
            self.inner_flush(FlushOptions::CurrentHeader)
        }
    }

    /// Flush uncommitted state to disk, but under the given block hash.
    pub fn flush_to(&mut self, bhh: &T) -> Result<(), Error> {
        self.inner_flush(FlushOptions::NewHeader(bhh))
    }

    /// Flush uncommitted state to disk for a mined block (i.e. not part of the chainstate, and not
    /// an ancestor of any block), and do so under a given block hash.
    pub fn flush_mined(&mut self, bhh: &T) -> Result<(), Error> {
        self.inner_flush(FlushOptions::MinedTable(bhh))
    }

    /// Drop the uncommitted state and any associated cached state.
    pub fn drop_extending_trie(&mut self) {
        self.clear_cached_ancestor_hashes_bytes();
        if !self.data.readonly {
            if let Some((ref bhh, _)) = self.data.uncommitted_writes.take() {
                trie_sql::drop_lock(&self.db, bhh)
                    .expect("Corruption: Failed to drop the extended trie lock");
            }
            self.data.uncommitted_writes = None;
            self.data.clear_block_id();
            self.data.trie_ancestor_hash_bytes_cache = None;
        }
    }

    /// Drop the unconfirmed state and uncommitted state.
    pub fn drop_unconfirmed_trie(&mut self, bhh: &T) {
        self.clear_cached_ancestor_hashes_bytes();
        if !self.data.readonly && self.data.unconfirmed {
            trie_sql::drop_unconfirmed_trie(&self.db, bhh)
                .expect("Corruption: Failed to drop unconfirmed trie");
            trie_sql::drop_lock(&self.db, bhh)
                .expect("Corruption: Failed to drop the extended trie lock");
            self.data.uncommitted_writes = None;
            self.data.clear_block_id();
            self.data.trie_ancestor_hash_bytes_cache = None;
        }
    }

    /// Seal the inner uncommitted TrieRAM and return the MARF root hash.
    /// Only works if there's an uncommitted TrieRAM extension; panics if not.
    pub fn seal(&mut self) -> Result<TrieHash, Error> {
        if let Some((bhh, trie_ram)) = self.data.uncommitted_writes.take() {
            let sealed_trie_ram = trie_ram.seal(self)?;
            let root_hash = match sealed_trie_ram {
                UncommittedState::Sealed(_, root_hash) => root_hash.clone(),
                _ => {
                    unreachable!("FATAL: .seal() did not make a sealed trieram");
                }
            };
            self.data.uncommitted_writes = Some((bhh, sealed_trie_ram));
            Ok(root_hash)
        } else {
            panic!("FATAL: tried to a .seal() a trie that was not extended");
        }
    }

    /// Extend the forest of Tries to include a new confirmed block.
    /// Fails if the block already exists, or if the storage is read-only, or open
    /// only for unconfirmed state.
    pub fn extend_to_block(&mut self, bhh: &T) -> Result<(), Error> {
        self.clear_cached_ancestor_hashes_bytes();
        if self.data.readonly {
            return Err(Error::ReadOnlyError);
        }
        if self.data.unconfirmed {
            return Err(Error::UnconfirmedError);
        }

        if self.get_block_id_caching(bhh).is_ok() {
            warn!("Block already exists: {}", &bhh);
            return Err(Error::ExistsError);
        }

        self.flush()?;

        let size_hint = match self.data.uncommitted_writes {
            Some((_, ref trie_storage)) => 2 * trie_storage.size_hint(),
            None => 1024, // don't try to guess _byte_ allocation here.
        };

        let trie_buf = TrieRAM::new(bhh, size_hint, &self.data.cur_block);

        // place a lock on this block, so we can't extend to it again
        if !trie_sql::lock_bhh_for_extension(self.sqlite_tx(), bhh, false)? {
            warn!("Block already extended: {}", &bhh);
            return Err(Error::ExistsError);
        }

        self.switch_trie(bhh, UncommittedState::RW(trie_buf));
        Ok(())
    }

    /// Extend the forest of Tries to include a new unconfirmed block.
    /// If the unconfirmed block (bhh) already exists, then load up its trie as the uncommitted_writes
    /// trie.
    pub fn extend_to_unconfirmed_block(&mut self, bhh: &T) -> Result<bool, Error> {
        self.clear_cached_ancestor_hashes_bytes();
        if !self.data.unconfirmed {
            return Err(Error::UnconfirmedError);
        }

        self.flush()?;

        // try to load up the trie
        let (trie_buf, created, unconfirmed_block_id) =
            if let Some(block_id) = trie_sql::get_unconfirmed_block_identifier(&self.db, bhh)? {
                debug!("Reload unconfirmed trie {} ({})", bhh, block_id);

                // restore trie
                let mut fd = trie_sql::open_trie_blob(&self.db, block_id)?;

                test_debug!("Unconfirmed trie block ID for {} is {}", bhh, block_id);
                (TrieRAM::load(&mut fd, bhh)?, false, Some(block_id))
            } else {
                debug!("Instantiate unconfirmed trie {}", bhh);

                // new trie
                let size_hint = match self.data.uncommitted_writes {
                    Some((_, ref trie_storage)) => 2 * trie_storage.size_hint(),
                    None => 1024, // don't try to guess _byte_ allocation here.
                };

                (
                    TrieRAM::new(bhh, size_hint, &self.data.cur_block),
                    true,
                    None,
                )
            };

        // place a lock on this block, so we can't extend to it again
        if !trie_sql::tx_lock_bhh_for_extension(&self.db, bhh, true)? {
            warn!("Block already extended: {}", &bhh);
            return Err(Error::ExistsError);
        }

        self.unconfirmed_block_id = unconfirmed_block_id;
        self.switch_trie(bhh, UncommittedState::RW(trie_buf));
        Ok(created)
    }

    /// Clear out the underlying storage.
    pub fn format(&mut self) -> Result<(), Error> {
        if self.data.readonly {
            return Err(Error::ReadOnlyError);
        }

        debug!("Format TrieFileStorage");

        // blow away db
        trie_sql::clear_tables(self.sqlite_tx())?;

        if let Some((_, ref mut trie_storage)) = self.data.uncommitted_writes {
            trie_storage.format()?
        };

        self.data.set_block(T::sentinel(), None);

        self.data.uncommitted_writes = None;
        self.clear_cached_ancestor_hashes_bytes();

        Ok(())
    }

    pub fn sqlite_tx(&self) -> &Transaction<'a> {
        match &self.0.db {
            SqliteConnection::Tx(ref tx) => tx,
            SqliteConnection::ConnRef(_) => {
                unreachable!(
                    "BUG: Constructed TrieStorageTransaction with a bare sqlite connection ref."
                );
            }
        }
    }

    pub fn sqlite_tx_mut(&mut self) -> &mut Transaction<'a> {
        match &mut self.0.db {
            SqliteConnection::Tx(ref mut tx) => tx,
            SqliteConnection::ConnRef(_) => {
                unreachable!(
                    "BUG: Constructed TrieStorageTransaction with a bare sqlite connection ref."
                );
            }
        }
    }

    pub fn commit_tx(self) {
        match self.0.db {
            SqliteConnection::Tx(tx) => {
                tx.commit().expect("CORRUPTION: Failed to commit MARF");
            }
            SqliteConnection::ConnRef(_) => {
                unreachable!(
                    "BUG: Constructed TrieStorageTransaction with a bare sqlite connection ref."
                );
            }
        }
    }

    pub fn rollback(self) {
        match self.0.db {
            SqliteConnection::Tx(tx) => {
                tx.rollback().expect("CORRUPTION: Failed to commit MARF");
            }
            SqliteConnection::ConnRef(_) => {
                unreachable!(
                    "BUG: Constructed TrieStorageTransaction with a bare sqlite connection ref."
                );
            }
        }
    }
}

impl<T: MarfTrieId> TrieStorageConnection<'_, T> {
    pub fn readonly(&self) -> bool {
        self.data.readonly
    }

    pub fn unconfirmed(&self) -> bool {
        self.data.unconfirmed
    }

    pub fn set_cached_ancestor_hashes_bytes(&mut self, bhh: &T, bytes: Vec<TrieHash>) {
        self.data.trie_ancestor_hash_bytes_cache = Some((bhh.clone(), bytes));
    }

    pub fn clear_cached_ancestor_hashes_bytes(&mut self) {
        self.data.trie_ancestor_hash_bytes_cache = None;
    }

    pub fn get_root_hash_at(&mut self, tip: &T) -> Result<TrieHash, Error> {
        let cur_block_hash = self.get_cur_block();

        self.open_block(tip)?;
        let root_hash_res = read_root_hash(self);

        // restore
        self.open_block(&cur_block_hash)?;
        root_hash_res
    }

    pub fn check_cached_ancestor_hashes_bytes(&mut self, bhh: &T) -> Option<Vec<TrieHash>> {
        if let Some((ref cached_bhh, ref cached_bytes)) = self.data.trie_ancestor_hash_bytes_cache {
            if cached_bhh == bhh {
                return Some(cached_bytes.clone());
            }
        }
        None
    }

    #[cfg(test)]
    pub fn stats(&mut self) -> (u64, u64) {
        let r = self.data.read_count;
        let w = self.data.write_count;
        self.data.read_count = 0;
        self.data.write_count = 0;
        (r, w)
    }

    #[cfg(test)]
    pub fn node_stats(&mut self) -> (u64, u64, u64) {
        let nr = self.data.read_node_count;
        let br = self.data.read_backptr_count;
        let nw = self.data.write_node_count;

        self.data.read_node_count = 0;
        self.data.read_backptr_count = 0;
        self.data.write_node_count = 0;

        (nr, br, nw)
    }

    #[cfg(test)]
    pub fn leaf_stats(&mut self) -> (u64, u64) {
        let lr = self.data.read_leaf_count;
        let lw = self.data.write_leaf_count;

        self.data.read_leaf_count = 0;
        self.data.write_leaf_count = 0;

        (lr, lw)
    }

    /// Recover from partially-written state -- i.e. blow it away.
    /// Doesn't get called automatically.
    pub fn recover(db_path: &String) -> Result<(), Error> {
        let conn = marf_sqlite_open(db_path, OpenFlags::SQLITE_OPEN_READ_WRITE, false)?;
        trie_sql::clear_lock_data(&conn)
    }

    /// Read the Trie root node's hash from the block table.
    #[cfg(test)]
    pub fn read_block_root_hash(&mut self, bhh: &T) -> Result<TrieHash, Error> {
        let root_hash_ptr = TriePtr::new(
            TrieNodeID::Node256 as u8,
            0,
            TrieStorageConnection::<T>::root_ptr_disk(),
        );
        if let Some(blobs) = self.blobs.as_mut() {
            // stored in a blobs file
            blobs.get_node_hash_bytes_by_bhh(&self.db, bhh, &root_hash_ptr)
        } else {
            // stored to DB
            trie_sql::get_node_hash_bytes_by_bhh(&self.db, bhh, &root_hash_ptr)
        }
    }

    #[cfg(test)]
    fn inner_read_persisted_root_to_blocks(&mut self) -> Result<HashMap<TrieHash, T>, Error> {
        let ret = match self.blobs.as_mut() {
            Some(blobs) => HashMap::from_iter(blobs.read_all_block_hashes_and_roots(&self.db)?),
            None => HashMap::from_iter(trie_sql::read_all_block_hashes_and_roots(&self.db)?),
        };
        Ok(ret)
    }

    /// Generate a mapping between Trie root hashes and the blocks that contain them
    #[cfg(test)]
    pub fn read_root_to_block_table(&mut self) -> Result<HashMap<TrieHash, T>, Error> {
        let mut ret = self.inner_read_persisted_root_to_blocks()?;
        let uncommitted_writes = match self.data.uncommitted_writes.take() {
            Some((bhh, trie_ram)) => {
                let ptr = TriePtr::new(set_backptr(TrieNodeID::Node256 as u8), 0, 0);

                let root_hash = trie_ram.read_node_hash(&ptr)?;

                ret.insert(root_hash.clone(), bhh.clone());
                Some((bhh, trie_ram))
            }
            _ => None,
        };

        self.data.uncommitted_writes = uncommitted_writes;

        Ok(ret)
    }

    /// internal procedure for locking a trie hash for work
    fn switch_trie(&mut self, bhh: &T, trie_buf: UncommittedState<T>) {
        trace!("Extended from {} to {}", &self.data.cur_block, bhh);

        // update internal structures
        self.data.set_block(bhh.clone(), None);
        self.clear_cached_ancestor_hashes_bytes();

        self.data.uncommitted_writes = Some((bhh.clone(), trie_buf));
    }

    /// Is the given block in the marf_data DB table, and is it part of the block history (i.e. it's not mined and
    /// its not unconfirmed)?
    pub fn has_confirmed_block(&self, bhh: &T) -> Result<bool, Error> {
        match trie_sql::get_confirmed_block_identifier(&self.db, bhh) {
            Ok(Some(_)) => Ok(true),
            Ok(None) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// Is the given block in the marf_data DB table, and is it unconfirmed?
    pub fn has_unconfirmed_block(&self, bhh: &T) -> Result<bool, Error> {
        match trie_sql::get_unconfirmed_block_identifier(&self.db, bhh) {
            Ok(Some(_)) => Ok(true),
            Ok(None) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// Is the given block represented in either the confirmed or unconfirmed block tables?
    /// The mined table is ignored.
    pub fn has_block(&self, bhh: &T) -> Result<bool, Error> {
        Ok(self.has_confirmed_block(bhh)? || self.has_unconfirmed_block(bhh)?)
    }

    /// Used for providing a option<block identifier> when re-opening a block --
    ///   because the previously open block may have been the uncommitted_writes block,
    ///   id may have been None.
    pub fn open_block_maybe_id(&mut self, bhh: &T, id: Option<u32>) -> Result<(), Error> {
        match id {
            Some(id) => self.open_block_known_id(bhh, id),
            None => self.open_block(bhh),
        }
    }

    /// Used for providing a block identifier when opening a block -- usually used
    ///   when following a backptr, which stores the block identifier directly.
    pub fn open_block_known_id(&mut self, bhh: &T, id: u32) -> Result<(), Error> {
        trace!(
            "open_block_known_id({},{}) (unconfirmed={:?},{})",
            bhh,
            id,
            &self.unconfirmed_block_id,
            self.unconfirmed()
        );
        if *bhh == self.data.cur_block && self.data.cur_block_id.is_some() {
            // no-op
            return Ok(());
        }

        if let Some((ref uncommitted_bhh, _)) = self.data.uncommitted_writes {
            if uncommitted_bhh == bhh {
                panic!("BUG: passed id of a currently building block");
            }
        }

        // opening a different Trie than the one we're extending
        self.data.set_block(bhh.clone(), Some(id));
        Ok(())
    }

    /// Open a trie's block, identified by `bhh`.  Updates the internal state to point to it, so
    /// that all node reads will occur relative to it.
    pub fn open_block(&mut self, bhh: &T) -> Result<(), Error> {
        trace!(
            "open_block({}) (unconfirmed={:?},{})",
            bhh,
            &self.unconfirmed_block_id,
            self.unconfirmed()
        );
        self.bench.open_block_start();

        if *bhh == self.data.cur_block && self.data.cur_block_id.is_some() {
            // no-op
            if self.unconfirmed()
                && self.data.cur_block_id
                    == trie_sql::get_unconfirmed_block_identifier(&self.db, bhh)?
            {
                test_debug!(
                    "{} unconfirmed trie block ID is {:?}",
                    bhh,
                    &self.data.cur_block_id
                );
                self.unconfirmed_block_id = self.data.cur_block_id.clone();
            }

            self.bench.open_block_finish(true);
            return Ok(());
        }

        let sentinel = T::sentinel();
        if *bhh == sentinel {
            // just reset to newly opened state
            // did we write to the sentinel?
            let block_id_opt = self.get_block_id_caching(bhh).ok();
            self.data.set_block(sentinel, block_id_opt);
            self.bench.open_block_finish(true);
            return Ok(());
        }

        if let Some((ref uncommitted_bhh, _)) = self.data.uncommitted_writes {
            if uncommitted_bhh == bhh {
                // nothing to do -- we're already ready.
                // just clear out.
                if self.unconfirmed()
                    && self.data.cur_block_id
                        == trie_sql::get_unconfirmed_block_identifier(&self.db, bhh)?
                {
                    test_debug!(
                        "{} unconfirmed trie block ID is {:?}",
                        bhh,
                        &self.data.cur_block_id
                    );
                    self.unconfirmed_block_id = self.data.cur_block_id.clone();
                }
                self.data.set_block(bhh.clone(), None);
                self.bench.open_block_finish(true);
                return Ok(());
            }
        }

        if self.unconfirmed() {
            if let Some(block_id) = trie_sql::get_unconfirmed_block_identifier(&self.db, bhh)? {
                // this is an unconfirmed trie being opened
                self.data.set_block(bhh.clone(), Some(block_id));
                self.bench.open_block_finish(false);

                // reads to this block will hit sqlite
                test_debug!("{} unconfirmed trie block ID is {}", bhh, block_id);
                self.unconfirmed_block_id = Some(block_id);
                return Ok(());
            }
        }

        // opening a different Trie than the one we're extending
        let block_id = self.get_block_id_caching(bhh).map_err(|e| {
            test_debug!("Failed to open {:?}: {:?}", bhh, e);
            e
        })?;

        self.data.set_block(bhh.clone(), Some(block_id));
        self.bench.open_block_finish(false);
        Ok(())
    }

    /// Return the block_identifier / row_id for a given bhh. If that bhh
    ///  is currently being extended, return None, since the row_id won't
    ///  be known until the extended trie is flushed.
    pub fn get_block_identifier(&mut self, bhh: &T) -> Option<u32> {
        if let Some((ref uncommitted_bhh, _)) = self.data.uncommitted_writes {
            if bhh == uncommitted_bhh {
                return None;
            }
        }

        self.get_block_id_caching(bhh).ok()
    }

    /// Get the currently-open block identifier (its row ID)
    pub fn get_cur_block_identifier(&mut self) -> Result<u32, Error> {
        if let Some((ref uncommitted_bhh, _)) = self.data.uncommitted_writes {
            if &self.data.cur_block == uncommitted_bhh {
                return Err(Error::RequestedIdentifierForExtensionTrie);
            }
        }

        self.data.cur_block_id.ok_or_else(|| Error::NotOpenedError)
    }

    /// Get the currently-open block hash
    pub fn get_cur_block(&self) -> T {
        self.data.cur_block.clone()
    }

    /// Get the currently-open block hash and block ID (row ID)
    pub fn get_cur_block_and_id(&self) -> (T, Option<u32>) {
        (self.data.cur_block.clone(), self.data.cur_block_id.clone())
    }

    /// Get the block hash of a given block ID (i.e. row ID)
    pub fn get_block_from_local_id(&mut self, local_id: u32) -> Result<&T, Error> {
        let res = self.get_block_hash_caching(local_id);
        res
    }

    /// Get the TriePtr::ptr() value for the root node in the currently-open block.
    pub fn root_ptr(&self) -> u32 {
        if let Some((ref uncommitted_bhh, _)) = self.data.uncommitted_writes {
            if &self.data.cur_block == uncommitted_bhh {
                return 0;
            }
        }

        TrieStorageConnection::<T>::root_ptr_disk()
    }

    /// Get a TriePtr to the currently-open block's trie's root node.
    pub fn root_trieptr(&self) -> TriePtr {
        TriePtr::new(TrieNodeID::Node256 as u8, 0, self.root_ptr())
    }

    /// Get the TriePtr::ptr() value for a trie's root node if the node is stored to disk.
    pub fn root_ptr_disk() -> u32 {
        // first 32 bytes are the block parent hash
        //   next 4 are the identifier
        (BLOCK_HEADER_HASH_ENCODED_SIZE as u32) + 4
    }

    /// Read a node's children's hashes into the provided <Write> implementation.
    /// This only works for intermediate nodes and leafs (the latter of which have no children).
    ///
    /// This method is designed to only access hashes that are either (1) in this Trie, or (2) in
    /// RAM already (i.e. as part of the block map)
    ///
    /// This means that the hash of a node that is in a previous Trie will _not_ be its
    /// hash (as that would require a disk access), but would instead be the root hash of the Trie
    /// that contains it.  While this makes the Merkle proof construction a bit more complicated,
    /// it _significantly_ improves the performance of this method (which is crucial since this is on
    /// the write path, which must be as short as possible).
    ///
    /// Rules:
    /// If a node is empty, pass in an empty hash.
    /// If a node is in this Trie, pass its hash.
    /// If a node is in a previous Trie, pass the root hash of its Trie.
    ///
    /// On err, S may point to a prior block.  The caller should call s.open(...) if an error
    /// occurs.
    ///
    /// NOTE: this method should only be called if `hash_calculation_mode` is set to
    /// `TrieHashCalculationMode::All` or `TrieHashCalculationMode::Immediate`.  There is no need
    /// to call if the hash mode is `::Deferred`.  The only way this gets called while not in
    /// `::Deferred` mode is when generating a Merkle proof.
    pub fn write_children_hashes<W: Write>(
        &mut self,
        node: &TrieNodeType,
        w: &mut W,
    ) -> Result<(), Error> {
        if self.data.readonly {
            return Err(Error::ReadOnlyError);
        }

        trace!("write_children_hashes for {:?}", node);

        let mut map = TrieSqlHashMapCursor {
            db: &self.db,
            cache: self.cache,
            unconfirmed: self.data.unconfirmed,
        };

        if let Some((ref uncommitted_bhh, ref mut uncommitted_trie)) = self.data.uncommitted_writes
        {
            if &self.data.cur_block == uncommitted_bhh {
                // storage currently points to uncommitted state
                let start_time = self.bench.write_children_hashes_start();
                let res = TrieStorageConnection::<T>::inner_write_children_hashes(
                    uncommitted_trie.trie_ram_mut(),
                    &mut map,
                    node,
                    w,
                    self.bench,
                );
                self.bench.write_children_hashes_finish(start_time, true);
                return res;
            }
        }

        // storage points to committed state
        if let Some(blobs) = self.blobs.as_mut() {
            // tries stored on file
            let start_time = self.bench.write_children_hashes_start();
            let block_id = self.data.cur_block_id.ok_or_else(|| {
                error!("Failed to get cur block as hash reader");
                Error::NotFoundError
            })?;
            let mut cursor = TrieFileNodeHashReader::new(&self.db, blobs, block_id);
            let res = TrieStorageConnection::<T>::inner_write_children_hashes(
                &mut cursor,
                &mut map,
                node,
                w,
                self.bench,
            );
            self.bench.write_children_hashes_finish(start_time, false);
            res
        } else {
            // tries stored in DB
            let start_time = self.bench.write_children_hashes_start();
            let mut cursor = TrieSqlCursor {
                db: &self.db,
                block_id: self.data.cur_block_id.ok_or_else(|| {
                    error!("Failed to get cur block as hash reader");
                    Error::NotFoundError
                })?,
            };
            let res = TrieStorageConnection::<T>::inner_write_children_hashes(
                &mut cursor,
                &mut map,
                node,
                w,
                self.bench,
            );
            self.bench.write_children_hashes_finish(start_time, false);
            res
        }
    }

    /// Inner method for calculating a node's hash, by hashing its children.
    fn inner_write_children_hashes<W: Write, H: NodeHashReader, M: BlockMap>(
        hash_reader: &mut H,
        map: &mut M,
        node: &TrieNodeType,
        w: &mut W,
        bench: &mut TrieBenchmark,
    ) -> Result<(), Error> {
        trace!("inner_write_children_hashes begin for node {:?}:", &node);
        for ptr in node.ptrs().iter() {
            if ptr.id() == TrieNodeID::Empty as u8 {
                // hash of empty string
                let start_time = bench.write_children_hashes_empty_start();

                trace!(
                    "inner_write_children_hashes for node {:?}: {:?} empty",
                    &node,
                    &ptr
                );
                w.write_all(TrieHash::from_data(&[]).as_bytes())?;

                bench.write_children_hashes_empty_finish(start_time);
            } else if !is_backptr(ptr.id()) {
                // hash is in the same block as this node
                let start_time = bench.write_children_hashes_same_block_start();

                let mut buf = Vec::with_capacity(TRIEHASH_ENCODED_SIZE);
                hash_reader.read_node_hash_bytes(ptr, &mut buf)?;
                trace!(
                    "inner_write_children_hashes for node {:?}: {:?} same block {}",
                    &node,
                    &ptr,
                    &to_hex(&buf)
                );
                w.write_all(&buf[..])?;

                bench.write_children_hashes_same_block_finish(start_time);
            } else {
                // hash is in a different block altogether, so we just use the ancestor block hash.  The
                // ptr.ptr() value points to the actual node in the ancestor block.
                let start_time = bench.write_children_hashes_ancestor_block_start();

                let block_hash = map.get_block_hash_caching(ptr.back_block())?;
                trace!(
                    "inner_write_children_hashes for node {:?}: {:?} back block {:?}",
                    &node,
                    &ptr,
                    &block_hash
                );
                w.write_all(block_hash.as_bytes())?;

                bench.write_children_hashes_ancestor_block_finish(start_time);
            }
        }
        trace!("inner_write_children_hashes end for node {:?}:", &node);

        Ok(())
    }

    /// read a persisted node's hash
    fn inner_read_persisted_node_hash(
        &mut self,
        block_id: u32,
        ptr: &TriePtr,
    ) -> Result<TrieHash, Error> {
        if self.unconfirmed_block_id == Some(block_id) {
            // read from unconfirmed trie
            test_debug!(
                "Read persisted node hash from unconfirmed block id {}",
                block_id
            );
            return trie_sql::get_node_hash_bytes(&self.db, block_id, ptr);
        }
        let node_hash = match self.blobs.as_mut() {
            Some(blobs) => blobs.get_node_hash_bytes(&self.db, block_id, ptr),
            None => trie_sql::get_node_hash_bytes(&self.db, block_id, ptr),
        }?;
        Ok(node_hash)
    }

    /// Read a persisted node's hash
    pub fn read_node_hash_bytes(&mut self, ptr: &TriePtr) -> Result<TrieHash, Error> {
        if let Some((ref uncommitted_bhh, ref mut trie_ram)) = self.data.uncommitted_writes {
            // special case
            if &self.data.cur_block == uncommitted_bhh {
                return trie_ram.read_node_hash(ptr);
            }
        }

        // some other block or ptr
        match self.data.cur_block_id {
            Some(block_id) => {
                self.bench.read_node_hash_start();
                if let Some(node_hash) = self.cache.load_node_hash(block_id, ptr) {
                    let res = node_hash;
                    self.bench.read_node_hash_finish(true);
                    Ok(res)
                } else {
                    let node_hash = self.inner_read_persisted_node_hash(block_id, ptr)?;
                    self.cache
                        .store_node_hash(block_id, ptr.clone(), node_hash.clone());
                    self.bench.read_node_hash_finish(false);
                    Ok(node_hash)
                }
            }
            None => {
                error!("Not found (no file is open)");
                Err(Error::NotFoundError)
            }
        }
    }

    /// Read a persisted node and its hash.
    pub fn read_nodetype(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        self.read_nodetype_maybe_hash(ptr, true)
    }

    /// Read a persisted node
    pub fn read_nodetype_nohash(&mut self, ptr: &TriePtr) -> Result<TrieNodeType, Error> {
        self.read_nodetype_maybe_hash(ptr, false)
            .map(|(node, _)| node)
    }

    /// Inner method for reading a node, and optionally its hash as well.
    /// Uses either the DB or the .blobs file, depending on which is configured.
    /// If `read_hash` is `false`, then the returned hash is just the empty hash of all 0's.
    fn inner_read_persisted_nodetype(
        &mut self,
        block_id: u32,
        ptr: &TriePtr,
        read_hash: bool,
    ) -> Result<(TrieNodeType, TrieHash), Error> {
        trace!(
            "inner_read_persisted_nodetype({block_id}): {ptr:?} (unconfirmed={:?},{})",
            &self.unconfirmed_block_id,
            self.unconfirmed()
        );
        if self.unconfirmed_block_id == Some(block_id) {
            trace!("Read persisted node from unconfirmed block id {block_id}");

            // read from unconfirmed trie
            if read_hash {
                return trie_sql::read_node_type(&self.db, block_id, ptr);
            } else {
                return trie_sql::read_node_type_nohash(&self.db, block_id, ptr)
                    .map(|node| (node, TrieHash([0u8; TRIEHASH_ENCODED_SIZE])));
            }
        }
        let (node_inst, node_hash) = match self.blobs.as_mut() {
            Some(blobs) => {
                if read_hash {
                    blobs.read_node_type(&self.db, block_id, ptr)?
                } else {
                    blobs
                        .read_node_type_nohash(&self.db, block_id, ptr)
                        .map(|node| (node, TrieHash([0u8; TRIEHASH_ENCODED_SIZE])))?
                }
            }
            None => {
                if read_hash {
                    trie_sql::read_node_type(&self.db, block_id, ptr)?
                } else {
                    trie_sql::read_node_type_nohash(&self.db, block_id, ptr)
                        .map(|node| (node, TrieHash([0u8; TRIEHASH_ENCODED_SIZE])))?
                }
            }
        };
        Ok((node_inst, node_hash))
    }

    /// Read a node and optionally its hash.  If `read_hash` is false, then an empty hash will be
    /// returned
    /// NOTE: ptr will not be treated as a backptr -- the node returned will be from the
    /// currently-open trie.
    fn read_nodetype_maybe_hash(
        &mut self,
        ptr: &TriePtr,
        read_hash: bool,
    ) -> Result<(TrieNodeType, TrieHash), Error> {
        trace!("read_nodetype({:?}): {:?}", &self.data.cur_block, ptr);

        self.data.read_count += 1;
        if is_backptr(ptr.id()) {
            self.data.read_backptr_count += 1;
        } else if ptr.id() == TrieNodeID::Leaf as u8 {
            self.data.read_leaf_count += 1;
        } else {
            self.data.read_node_count += 1;
        }

        let clear_ptr = ptr.from_backptr();

        if let Some((ref uncommitted_bhh, ref mut uncommitted_trie)) = self.data.uncommitted_writes
        {
            // special case
            if &self.data.cur_block == uncommitted_bhh {
                return uncommitted_trie.read_nodetype(&clear_ptr);
            }
        }

        // some other block
        match self.data.cur_block_id {
            Some(id) => {
                self.bench.read_nodetype_start();
                let (node_inst, node_hash) = if read_hash {
                    if let Some((node_inst, node_hash)) =
                        self.cache.load_node_and_hash(id, &clear_ptr)
                    {
                        (node_inst, node_hash)
                    } else {
                        let (node_inst, node_hash) =
                            self.inner_read_persisted_nodetype(id, &clear_ptr, read_hash)?;
                        self.cache.store_node_and_hash(
                            id,
                            clear_ptr.clone(),
                            node_inst.clone(),
                            node_hash.clone(),
                        );
                        (node_inst, node_hash)
                    }
                } else if let Some(node_inst) = self.cache.load_node(id, &clear_ptr) {
                    (node_inst, TrieHash([0u8; TRIEHASH_ENCODED_SIZE]))
                } else {
                    let (node_inst, _) =
                        self.inner_read_persisted_nodetype(id, &clear_ptr, read_hash)?;
                    self.cache
                        .store_node(id, clear_ptr.clone(), node_inst.clone());
                    (node_inst, TrieHash([0u8; TRIEHASH_ENCODED_SIZE]))
                };

                self.bench.read_nodetype_finish(false);
                Ok((node_inst, node_hash))
            }
            None => {
                debug!("Not found (no file is open)");
                Err(Error::NotFoundError)
            }
        }
    }

    /// Store a node and its hash to the uncommitted state.
    /// If the uncommitted state is not instantiated, then this panics.
    pub fn write_nodetype(
        &mut self,
        disk_ptr: u32,
        node: &TrieNodeType,
        hash: TrieHash,
    ) -> Result<(), Error> {
        if self.data.readonly {
            return Err(Error::ReadOnlyError);
        }

        trace!(
            "write_nodetype({:?}): at {}: {:?} {:?}",
            &self.data.cur_block,
            disk_ptr,
            &hash,
            node
        );

        self.data.write_count += 1;
        match node {
            TrieNodeType::Leaf(_) => {
                self.data.write_leaf_count += 1;
            }
            _ => {
                self.data.write_node_count += 1;
            }
        }

        // Only allow writes when the cur_block is the current in-RAM extending block.
        if let Some((ref uncommitted_bhh, ref mut uncommitted_trie)) = self.data.uncommitted_writes
        {
            if &self.data.cur_block == uncommitted_bhh {
                return uncommitted_trie.write_nodetype(disk_ptr, node, hash);
            }
        }

        panic!("Tried to write to another Trie besides the currently-buffered one.  This should never happen -- only flush() can write to disk!");
    }

    /// Store a node and its hash to uncommitted state.
    pub fn write_node<N: TrieNode + std::fmt::Debug>(
        &mut self,
        ptr: u32,
        node: &N,
        hash: TrieHash,
    ) -> Result<(), Error> {
        if self.data.readonly {
            return Err(Error::ReadOnlyError);
        }

        let node_type = node.as_trie_node_type();
        self.write_nodetype(ptr, &node_type, hash)
    }

    /// Get the last slot into which a node will be inserted in the uncommitted state.
    /// Panics if there is no uncommmitted state instantiated.
    pub fn last_ptr(&mut self) -> Result<u32, Error> {
        if let Some((_, ref mut uncommitted_trie)) = self.data.uncommitted_writes {
            uncommitted_trie.last_ptr()
        } else {
            panic!("Cannot allocate new ptrs in a Trie that is not in RAM");
        }
    }

    /// Count up the number of trie blocks this storage represents
    pub fn num_blocks(&self) -> usize {
        let result = if self.data.uncommitted_writes.is_some() {
            1
        } else {
            0
        };
        result
            + (trie_sql::count_blocks(&self.db)
                .expect("Corruption: SQL Error on a non-fallible query.") as usize)
    }

    pub fn get_benchmarks(&self) -> TrieBenchmark {
        self.bench.clone()
    }

    pub fn bench_mut(&mut self) -> &mut TrieBenchmark {
        self.bench
    }

    pub fn reset_benchmarks(&mut self) {
        self.bench.reset();
    }

    #[cfg(test)]
    pub fn transient_data(&self) -> &TrieStorageTransientData<T> {
        self.data
    }

    #[cfg(test)]
    pub fn transient_data_mut(&mut self) -> &mut TrieStorageTransientData<T> {
        self.data
    }
}
