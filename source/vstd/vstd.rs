//! The "standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and datatypes for proofs,
//! as well as runtime functionality with specifications.
//! For an introduction to Verus, see [the tutorial](https://verus-lang.github.io/verus/guide/).
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
#![cfg_attr(verus_keep_ghost, feature(allocator_api))]
#![cfg_attr(verus_keep_ghost, feature(step_trait))]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod arithmetic;
pub mod array;
pub mod atomic;
pub mod atomic_ghost;
pub mod bytes;
pub mod calc_macro;
pub mod cell;
pub mod function;
pub mod invariant;
pub mod layout;
pub mod map;
pub mod map_lib;
pub mod math;
pub mod modes;
pub mod multiset;
pub mod option;
pub mod pervasive;
#[cfg(feature = "alloc")]
pub mod ptr;
pub mod result;
pub mod seq;
pub mod seq_lib;
pub mod set;
pub mod set_lib;
pub mod slice;
pub mod state_machine_internal;
pub mod string;
#[cfg(feature = "std")]
pub mod thread;
#[cfg(feature = "alloc")]
pub mod vec;
pub mod view;

pub mod relations;
#[cfg(verus_keep_ghost)]
pub mod std_specs;

// Re-exports all vstd types, traits, and functions that are commonly used or replace
// regular `core` or `std` definitions.
pub mod prelude;

use prelude::*;

verus! {

#[verifier::broadcast_use_by_default_when_this_crate_is_imported]
pub broadcast group vstd_axioms {
    seq::seq_axioms,
    seq_lib::seq_lib_default,
    map::map_axioms,
    set::set_axioms,
    set_lib::set_lib_axioms,
    std_specs::bits::bits_axioms,
    std_specs::control_flow::control_flow_axioms,
    vec::vec_axioms,
    std_specs::vec::vec_axioms,
    array::array_axioms,
    multiset::multiset_axioms,
    string::string_axioms,
    ptr::ptr_axioms,
    std_specs::range::range_axioms,
}

} // verus!