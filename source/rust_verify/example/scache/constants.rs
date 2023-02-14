#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus!{

pub const NOT_MAPPED: u32 = 0xffff_ffff;

pub struct Config {
    pub cache_size: u32
}

impl Config {
    pub open spec fn valid_cache_ref(self, cache_ref: u32) -> bool {
        ||| 0 <= (cache_ref as int) < self.cache_size
        ||| cache_ref == NOT_MAPPED
    }
}

}
