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
    WriteInput{key: DiskIdx, data: Seq<u8>},
    ReadInput{key: DiskIdx},
    SyncInput{keys: Set<Key>},
    HavocInput{key: DiskIdx},
}

#[is_variant]
pub enum Output {
    WriteOutput,
    ReadOutput{data: Seq<u8>},
    SyncOutput,
    HavocOutput{key: DiskIdx},   // TODO: jonh doesn't understand why something's being returned here
}

pub type Block = Seq<u8>;

pub struct DiskIdx(pub nat);
// TODO define spec_lt on DiskIdx and get rid of .0s
pub struct CacheIdx(pub nat);
type SyncReq = Set<DiskIdx>;

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

    transition!{
        finish_read(cache_idx: CacheIdx, disk_idx: DiskIdx) {
            remove entries -= [ cache_idx => Entry::Reading{disk_idx} ];
            remove read_resps -= [ disk_idx => let data ];
            add entries += [ cache_idx => Entry::Entry{disk_idx, data} ];
            add statuses += [ cache_idx => Status::Clean ];
        }
    }

    transition!{
        start_writeback(cache_idx: CacheIdx) {
            remove statuses -= [ cache_idx => Status::Dirty ];
            have entries >= [ cache_idx => let Entry::Entry{disk_idx, data} ];
            
            add statuses += [ cache_idx => Status::Writeback ];
            add write_reqs += [ disk_idx => data ];
        }
    }

    transition!{
        finish_writeback(cache_idx: CacheIdx) {
            remove statuses -= [ cache_idx => Status::Writeback ];
            have entries >= [ cache_idx => let Entry::Entry{disk_idx, data} ];
            remove write_resps -= set { disk_idx };

            add statuses += [ cache_idx => Status::Clean ];
        }
    }

    transition!{
        evict(cache_idx: CacheIdx) {
            remove statuses -= [ cache_idx => Status::Clean ];
            remove entries -= [ cache_idx => let Entry::Entry{disk_idx, data} ];
            remove disk_idx_to_cache_idx -= [ disk_idx => let _ ];
            add entries += [ cache_idx => Entry::Empty ];
            add disk_idx_to_cache_idx += [ disk_idx => None ];
        }
    }

    transition!{
        observe_clean_for_sync(cache_idx: CacheIdx, rid: RequestId) {
            have statuses >= [ cache_idx => Status::Clean ];
            have entries >= [ cache_idx => let Entry::Entry{disk_idx, data} ];
            remove sync_reqs -= [ rid => let old_sync_reqs ];
            add sync_reqs += [ rid => old_sync_reqs.remove(disk_idx) ];
        }
    }

    transition!{
        apply_read(cache_idx: CacheIdx, rid: RequestId) {
            have entries >= [ cache_idx => let Entry::Entry{disk_idx, data} ];
            remove tickets -= [ rid => Input::ReadInput{key: disk_idx} ];
            add stubs += [ rid => Output::ReadOutput{data} ];
        }
    }

    transition!{
        apply_write(cache_idx: CacheIdx, rid: RequestId) {
            have entries >= [ cache_idx => let Entry::Entry{disk_idx, data} ];
            have statuses >= [ cache_idx => Status::Dirty ];
            remove tickets -= [ rid => Input::WriteInput{key: disk_idx, data} ];
            require data.len() == 4096;  // TODO(travis): why here?
            add stubs += [ rid => Output::WriteOutput ];
        }
    }

    transition!{
        mark_dirty(cache_idx: CacheIdx) {
            remove statuses -= [ cache_idx => Status::Clean ];
            add statuses += [ cache_idx => Status::Dirty ];
        }
    }

    transition!{
        havoc_new(cache_idx: CacheIdx, rid: RequestId, data: Block) {
            remove entries -= [ cache_idx => Entry::Empty ];
            have havocs >= [ rid => let disk_idx ];
            remove disk_idx_to_cache_idx -= [ disk_idx => None ];

            add entries += [ cache_idx => Entry::Entry{ disk_idx, data} ];

            // TODO(travis): why did this inherent-safety-condition need triggering?
            birds_eye let all_statuses = pre.statuses;
            assert(!all_statuses.contains_key(cache_idx)) by {
            };

            add statuses += [ cache_idx => Status::Dirty ];
            add disk_idx_to_cache_idx += [ disk_idx => Some(cache_idx) ];
        }
    }

    transition!{
        havoc_evict(cache_idx: CacheIdx, rid: RequestId) {
            remove statuses -= [ cache_idx => let status ];
            require status !== Status::Writeback;
            have havocs >= [ rid => let disk_idx ];
            remove entries -= [ cache_idx => let Entry::Entry{disk_idx: entry_disk_idx, data} ];
            require disk_idx === entry_disk_idx;
            remove disk_idx_to_cache_idx -= [ disk_idx => let ignore_ ];

            add entries += [ cache_idx => Entry::Empty ];
            add disk_idx_to_cache_idx += [ disk_idx => None ];
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
        forall |disk_idx|
        {
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
        // TODO(andrea,chris): I originally wrote this as a <==>
        // double-ended implication, and had all kinds of triggering trouble.
        &&& forall |cache_idx| {
                &&& self.entries.contains_key(cache_idx)
                &&& self.entries[cache_idx].is_Entry()
            } ==> self.statuses.contains_key(cache_idx)
        &&& forall |cache_idx| self.statuses.contains_key(cache_idx)
            ==> {
                &&& self.entries.contains_key(cache_idx)
                &&& self.entries[cache_idx].is_Entry()
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
        // disk_index_consistency_invariant
        assert forall |di|
            // A truckload of boilerplate...
        {
            &&& post.disk_idx_to_cache_idx.contains_key(di)
            &&& post.disk_idx_to_cache_idx[di].is_Some()
        } implies {
            let cache_idx = post.disk_idx_to_cache_idx[di].get_Some_0();
            &&& post.entries.contains_key(cache_idx)
            &&& post.entries[cache_idx] !== Entry::Empty
            &&& post.entries[cache_idx].get_disk_idx() === di
        } by {
            if disk_idx !== di {
                assert( pre.disk_idx_to_cache_idx.contains_key(di));    // to write this hypothesis trigger. :v(
                // (Which Dafny gets for free.)
            }
        }
    }

    #[inductive(finish_read)]
    fn finish_read_inductive(pre: Self, post: Self, cache_idx: CacheIdx, disk_idx: DiskIdx) {
        // statuses_invariant
        assume(post.statuses_invariant());  // flaky; ignoring
        assert forall |ci| {
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci].is_Entry()
        } <==> {
            post.statuses.contains_key(ci)
        } by {
            if ci !== cache_idx {
                assert(pre.entries.contains_key(ci) || true);   // gratuitous trigger
            }
        }
        // Dafny gets this proof with {}
    }

    #[inductive(start_writeback)]
    fn start_writeback_inductive(pre: Self, post: Self, cache_idx: CacheIdx) {
        // statuses_invariant
        assert forall |ci| {
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci].is_Entry()
        } <==> {
            post.statuses.contains_key(ci)
        } by {
            if ci !== cache_idx {
                assert(pre.entries.contains_key(ci) || true);   // gratuitous trigger
            }
        }
    }

    #[inductive(finish_writeback)]
    fn finish_writeback_inductive(pre: Self, post: Self, cache_idx: CacheIdx) {
        // disk_index_consistency_invariant
        let disk_idx = pre.entries[cache_idx].get_Entry_disk_idx();
        assert forall |di|
            // A truckload of boilerplate...
        {
            &&& post.disk_idx_to_cache_idx.contains_key(di)
            &&& post.disk_idx_to_cache_idx[di].is_Some()
        } implies {
            let ci = post.disk_idx_to_cache_idx[di].get_Some_0();
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci] !== Entry::Empty
            &&& post.entries[ci].get_disk_idx() === di
        } by {
            if disk_idx !== di {
                assert( pre.disk_idx_to_cache_idx.contains_key(di));    // to write this hypothesis trigger. :v(
            }
        }

        // statuses_invariant
        assert forall |ci| {
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci].is_Entry()
        } <==> {
            post.statuses.contains_key(ci)
        } by {
            if ci !== cache_idx {
                assert(pre.entries.contains_key(ci) || true);   // gratuitous trigger
                assume(false);  // this proof be flakin'
            }
        }
    }

    #[inductive(evict)]
    fn evict_inductive(pre: Self, post: Self, cache_idx: CacheIdx) {
        // disk_index_consistency_invariant
        let disk_idx = pre.entries[cache_idx].get_Entry_disk_idx();
        assert forall |di|
            // A truckload of boilerplate...
        {
            &&& post.disk_idx_to_cache_idx.contains_key(di)
            &&& post.disk_idx_to_cache_idx[di].is_Some()
        } implies {
            let ci = post.disk_idx_to_cache_idx[di].get_Some_0();
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci] !== Entry::Empty
            &&& post.entries[ci].get_disk_idx() === di
        } by {
            if disk_idx !== di {
                assert( pre.disk_idx_to_cache_idx.contains_key(di));    // to write this hypothesis trigger. :v(
            }
        }
        assume(post.statuses_invariant());  // flaky; ignoring
    }

    #[inductive(observe_clean_for_sync)]
    fn observe_clean_for_sync_inductive(pre: Self, post: Self, cache_idx: CacheIdx, rid: RequestId) {
    }

    #[inductive(apply_read)]
    fn apply_read_inductive(pre: Self, post: Self, cache_idx: CacheIdx, rid: RequestId) {
    }

    #[inductive(apply_write)]
    fn apply_write_inductive(pre: Self, post: Self, cache_idx: CacheIdx, rid: RequestId) { }

    #[inductive(mark_dirty)]
    fn mark_dirty_inductive(pre: Self, post: Self, cache_idx: CacheIdx) {
        assume(post.statuses_invariant());  // flaky; ignoring
    }
    
    #[inductive(havoc_new)]
    fn havoc_new_inductive(pre: Self, post: Self, cache_idx: CacheIdx, rid: RequestId, data: Block) {
        // disk_index_consistency_invariant
        let disk_idx = pre.havocs[rid];
        assert forall |di|
            // A truckload of boilerplate...
        {
            &&& post.disk_idx_to_cache_idx.contains_key(di)
            &&& post.disk_idx_to_cache_idx[di].is_Some()
        } implies {
            let ci = post.disk_idx_to_cache_idx[di].get_Some_0();
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci] !== Entry::Empty
            &&& post.entries[ci].get_disk_idx() === di
        } by {
            if disk_idx !== di {
                assert( pre.disk_idx_to_cache_idx.contains_key(di));    // to write this hypothesis trigger. :v(
            }
        }

        // statuses_invariant
        assert forall |ci| post.statuses.contains_key(ci)
            implies {
                &&& post.entries.contains_key(ci)
                &&& post.entries[ci].is_Entry()
            }  by {
            if ci!==cache_idx {
                assert( pre.statuses.contains_key(ci) );
            }
        }
    }
    
    #[inductive(havoc_evict)]
    fn havoc_evict_inductive(pre: Self, post: Self, cache_idx: CacheIdx, rid: RequestId) {
        // disk_index_consistency_invariant
        let disk_idx = pre.havocs[rid];
        assert forall |di|
            // A truckload of boilerplate...
        {
            &&& post.disk_idx_to_cache_idx.contains_key(di)
            &&& post.disk_idx_to_cache_idx[di].is_Some()
        } implies {
            let ci = post.disk_idx_to_cache_idx[di].get_Some_0();
            &&& post.entries.contains_key(ci)
            &&& post.entries[ci] !== Entry::Empty
            &&& post.entries[ci].get_disk_idx() === di
        } by {
            if disk_idx !== di {
                assert( pre.disk_idx_to_cache_idx.contains_key(di));    // to write this hypothesis trigger. :v(
            }
        }

        // statuses_invariant
        assert forall |ci| post.statuses.contains_key(ci)
            implies {
                &&& post.entries.contains_key(ci)
                &&& post.entries[ci].is_Entry()
            }  by {
            if ci!==cache_idx {
                assert( pre.statuses.contains_key(ci) );
            }
        }
    }
    
}

} //tokenized_state_machine

fn main() { }
