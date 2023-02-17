// rust_verify/tests/example.rs ignore
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::prelude::*;
use crate::pervasive::atomic_ghost::*;

// TODO(travis): "that should be fixed"
use crate::atomic_with_ghost;
use crate::atomic_with_ghost_inner;
use crate::atomic_with_ghost_load;

use state_machines_macros::tokenized_state_machine;
//use option::Option::{Some, None};

use crate::cache::*;
use crate::constants::*;

// TODO(travis): waiting on some fix to the atomic_with_ghost! macro.
verus_old_todo_no_ghost_blocks!{

// This macro generates the machinery that was handwritten in
// scache/cache/CacheResources.i.dfy
struct_with_invariants!{
    // This ports AtomicIndexLookup
    pub struct DiskIndexTableEntry {
        pub atomic: AtomicU32<
            _,  // macro fills in the AtomicInvariant trait here to embed the wf invariant
            Cache::disk_idx_to_cache_idx,   // the ghost type we're accessing atomically
            _   // macro fills in: invariant needs to be parameterized by a constant
        >,

        // TODO(travis): Expected to be able to use 'proof' keyword here
        #[proof] pub instance: Cache::Instance,

        #[spec] disk_idx: nat,
        #[spec] config: Config,
    }

    // This is the translation of state_inv
    spec fn wf(&self) -> bool {
        invariant on atomic with (instance, config) is (v: u32, g: Cache::disk_idx_to_cache_idx) {
            &&& config.valid_cache_ref(v)
            &&& g@.instance == instance
            &&& g@.key == DiskIdx(v as nat)
            &&& g@.value == if v == NOT_MAPPED { None } else { Some(CacheIdx(v as nat)) }
        }
    }
}

impl DiskIndexTableEntry {
    // TODO skipped this transition
    // Read, but we already know the answer(!).
    //fn read_known_cache_idx(&self, disk_idx: Ghost<nat>, config: Ghost<Config>,

    fn read(&self, disk_idx: Ghost<nat>) -> (cache_idx: u32)
    requires
      self.wf()
    ensures
      self.config.valid_cache_ref(cache_idx)
    {
        let cache_idx = atomic_with_ghost!(
            self.atomic => load();
            ghost g => {
            }
        );
        cache_idx
    }

    /*
    fn clear_mapping(&self, disk_idx: Ghost<nat>,
      cache_entry: Trk<CacheEntry>, status: Trk<CacheStatus>)
      -> (cache_empty: Trk<CacheEmpty>)
    requires
      self.wf(),
      status.is_Clean(),
      cache_entry.is_CacheEntry(),
      cache_entry.get_Entry_CacheIdx
      */  
}

} //verus

fn main() { }
