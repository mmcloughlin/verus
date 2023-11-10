#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_structural_vec verus_code! {
        use vstd::prelude::*;

        fn c(a: Vec<u8>, b: Vec<u8>)
            requires a@ == b@
        {
            if a == b {
                assert(true);
            } else {
                unreached()
            }
        }
    } => Ok(())
}
