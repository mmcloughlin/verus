#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus!{

const NOT_MAPPED: u32 = 0xffff_ffff;

struct Config {
    cache_size: u32
}

impl Config {
    pub open spec fn valid_cache_ref(self, cache_ref: u32) -> bool {
        ||| 0 <= (v as int) < self.cache_size
        ||| v == NOT_MAPPED
    }
}

}
