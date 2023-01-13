// rust_verify/tests/example.rs ignore
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::vec::*;
use pervasive::modes::*;
use pervasive::multiset::*;
use pervasive::map::*;
use pervasive::seq::*;
use pervasive::set::*;
use pervasive::option::*;
use pervasive::atomic_ghost::*;

use state_machines_macros::tokenized_state_machine;
use option::Option::{Some, None};

verus!{

// TODO factor into trusted framework
pub struct RequestId(nat);
pub struct Key(nat);

#[is_variant]
pub enum Input {
    WriteInput{key: Key, data: Seq<u8>},
    ReadInput{key: Key},
    SyncInput{keys: Set<Key>},
    HavocInput{key: Key},
}

#[is_variant]
pub enum Output {
    WriteOuput,
    ReadOuput{data: Seq<u8>},
    SyncOuput,
    HavocOuput{key: Key},   // TODO: jonh doesn't understand why something's being returned here
}

pub type Block = Seq<u8>;

pub struct DiskIdx(pub nat);
// TODO define spec_lt on DiskIdx and get rid of .0s
pub struct CacheIdx(pub nat);
pub struct SyncReq(Set<DiskIdx>);

pub enum Status { Clean, Dirty, Writeback }

#[is_variant]
pub enum Entry {
    Empty,
    Reading{disk_idx: DiskIdx},
    Entry{disk_idx: DiskIdx, data: Block}
}

impl Entry {
    pub  open spec fn get_disk_idx(self) -> DiskIdx
        recommends self !== Entry::Empty
    {
        match self {
            Entry::Empty => DiskIdx(0),
            Entry::Reading{disk_idx} => disk_idx,
            Entry::Entry{disk_idx, ..} => disk_idx,
        }
    }
}

pub spec const MAX_DISK_PAGES:nat = 0xffff_ffff_ffff_ffff;
pub spec const MAX_CACHE_SIZE:nat = 0xffff_ffff;

// TODO: move to map_v.rs
impl<K, V> Map<K, V> {
    pub open spec fn contains_key(self, key: K) -> bool {
        self.dom().contains(key)
    }
}

} // verus

tokenized_state_machine!{

Cache {
    fields {
        #[sharding(map)]
        pub disk_idx_to_cache_idx: Map<DiskIdx, Option<CacheIdx>>,

        #[sharding(map)]
        pub entries: Map<CacheIdx, Entry>,

        #[sharding(map)]
        pub statuses: Map<CacheIdx, Status>,

        #[sharding(map)]
        pub write_reqs: Map<DiskIdx, Block>,

        #[sharding(set)]
        pub write_resps: Set<DiskIdx>,
        
        #[sharding(set)]
        pub read_reqs: Set<DiskIdx>,
        
        #[sharding(map)]
        pub read_resps: Map<DiskIdx, Block>,

        #[sharding(map)]
        pub tickets: Map<RequestId, Input>,

        #[sharding(map)]
        pub stubs: Map<RequestId, Output>,

        #[sharding(map)]
        pub sync_reqs: Map<RequestId, SyncReq>,

        #[sharding(map)]
        pub havocs: Map<RequestId, DiskIdx>,
    }

    init!{
        initialize() {
            init disk_idx_to_cache_idx = Map::new(|idx: DiskIdx| idx.0 < MAX_DISK_PAGES, |idx| None);
            init entries = Map::new(|idx: CacheIdx| idx.0 < MAX_CACHE_SIZE, |idx| Entry::Empty);
            init statuses = Map::empty();
            init write_reqs = Map::empty();
            init write_resps = Set::empty();
            init read_reqs = Set::empty();
            init read_resps = Map::empty();
            init tickets = Map::empty();
            init stubs = Map::empty();
            init sync_reqs = Map::empty();
            init havocs = Map::empty();
        }
    }

    transition!{
        start_read(cache_idx: CacheIdx, disk_idx: DiskIdx) {
            remove entries -= [ cache_idx => Entry::Empty ];
            remove disk_idx_to_cache_idx -= [ disk_idx => None ];
            add entries += [ cache_idx => Entry::Reading{disk_idx} ];
            add disk_idx_to_cache_idx += [ disk_idx => Some(cache_idx) ];
            add read_reqs += set {disk_idx};
        }
    }

    //////////////////////////////////////////////////////////////////////////////
    // invariants
    //////////////////////////////////////////////////////////////////////////////

    #[invariant]
    pub spec fn cache_index_consistency_invariant(&self) -> bool {
        forall |cache_idx| {
            &&& self.entries.contains_key(cache_idx)
            &&& self.entries[cache_idx] !== Entry::Empty
        } ==> {
            &&& self.disk_idx_to_cache_idx.contains_key(self.entries[cache_idx].get_disk_idx())
            &&& self.disk_idx_to_cache_idx[self.entries[cache_idx].get_disk_idx()] === Some(cache_idx)
        }
    }

    #[invariant]
    pub spec fn disk_index_consistency_invariant(&self) -> bool {
        forall |disk_idx| {
            &&& self.disk_idx_to_cache_idx.contains_key(disk_idx)
            &&& self.disk_idx_to_cache_idx[disk_idx].is_Some()
        } ==> {
            let cache_idx = self.disk_idx_to_cache_idx[disk_idx].get_Some_0();
            &&& self.entries.contains_key(cache_idx)
            &&& self.entries[cache_idx] !== Entry::Empty
            &&& self.entries[cache_idx].get_disk_idx() === disk_idx
        }
    }

    #[invariant]
    pub spec fn disjoint_io_invariant(&self) -> bool {
        &&& self.read_reqs.disjoint(self.read_resps.dom())
        &&& self.write_reqs.dom().disjoint(self.write_resps)
    }

    #[invariant]
    pub spec fn read_io_invariant(&self) -> bool {
        forall |disk_idx| {
            &&& self.read_reqs.contains(disk_idx) || self.read_resps.contains_key(disk_idx)
        } ==> {
            &&& self.disk_idx_to_cache_idx.contains_key(disk_idx)
            &&& self.disk_idx_to_cache_idx[disk_idx].is_Some()
            &&& self.entries[self.disk_idx_to_cache_idx[disk_idx].get_Some_0()].is_Reading()
        }
    }

    #[invariant]
    pub spec fn write_io_invariant(&self) -> bool {
        forall |disk_idx| {
            &&& self.write_reqs.contains_key(disk_idx) || self.write_resps.contains(disk_idx)
        } ==> {
            let cache_idx = self.disk_idx_to_cache_idx[disk_idx].get_Some_0();
            &&& self.disk_idx_to_cache_idx.contains_key(disk_idx)
            &&& self.disk_idx_to_cache_idx[disk_idx].is_Some()
            &&& self.statuses.contains_key(cache_idx)
            &&& self.statuses[cache_idx] === Status::Writeback
        }
    }

    #[invariant]
    pub spec fn statuses_invariant(&self) -> bool {
        forall |cache_idx| {
            &&& self.entries.contains_key(cache_idx)
            &&& self.entries[cache_idx].is_Entry()
        } <==> {
            self.statuses.contains_key(cache_idx)
        }
    }

    #[invariant]
    pub spec fn disjoint_tickets_invariant(&self) -> bool {
        self.tickets.dom().disjoint(self.stubs.dom())
    }

    //////////////////////////////////////////////////////////////////////
    // init inductiveness proofs
    //////////////////////////////////////////////////////////////////////
    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
    }
       
    //////////////////////////////////////////////////////////////////////
    // transition inductiveness proofs
    //////////////////////////////////////////////////////////////////////
    #[inductive(start_read)]
    fn start_read_inductive(pre: Self, post: Self, cache_idx: CacheIdx, disk_idx: DiskIdx) {
        assert forall |disk_idx| {
            &&& self.disk_idx_to_cache_idx.contains_key(disk_idx)
            &&& self.disk_idx_to_cache_idx[disk_idx].is_Some()
        } implies {
            let cache_idx = self.disk_idx_to_cache_idx[disk_idx].get_Some_0();
            &&& self.entries.contains_key(cache_idx)
            &&& self.entries[cache_idx] !== Entry::Empty
            &&& self.entries[cache_idx].get_disk_idx() === disk_idx
        } by {
        }
    }
}

} //tokenized_state_machine

fn main() { }
