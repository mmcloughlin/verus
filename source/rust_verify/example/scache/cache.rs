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

pub enum Entry {
    Empty,
    Reading{disk_idx: DiskIdx},
    Entry{disk_idx: DiskIdx, data: Block}
}

pub spec const MAX_DISK_PAGES:nat = 0xffff_ffff_ffff_ffff;
pub spec const MAX_CACHE_SIZE:nat = 0xffff_ffff;

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
}

} //tokenized_state_machine

fn main() { }
