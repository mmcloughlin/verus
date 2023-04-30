#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Use external_fn_specification on an external function from the same crate

test_verify_one_file! {
    #[test] test_basics verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test1() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == false);
        }

        fn test2() {
            let ret_b = negate_bool(true, 0); // FAILS
        }

        fn test3() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == true); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// Apply external_fn_specification on a function from an external crate
// don't import vstd for this test (it would cause overlap)

test_verify_one_file! {
    #[test] test_apply_spec_to_external verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Import a specification from vstd of a function from std

test_verify_one_file! {
    #[test] test_import_spec_from_vstd verus_code! {
        use vstd::*;

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Test for overlap

test_verify_one_file! {
    #[test] test_overlap verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures2(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `crate::negate_bool`")
}

test_verify_one_file! {
    #[test] test_overlap2 verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures2<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

test_verify_one_file! {
    #[test] test_overlap3 verus_code! {
        use vstd::*;

        // This will conflict with the mem::swap specification declared in vstd
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

// Test sane error message if you call a proxy

test_verify_one_file! {
    #[test] test_call_proxy verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test() {
            negate_bool_requires_ensures(false, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external_fn_specification` directly; call `negate_bool` instead")
}

test_verify_one_file! {
    #[test] test_call_proxy2 verus_code! {
        fn test() {
            let x: u8 = 5;
            let y: u8 = 7;
            vstd::std_specs::core::ex_swap(&mut x, &mut y);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external_fn_specification` directly; call `core::mem::swap` instead")
}

// Recommends checking
// TODO do we have a way to write tests about 'recommends' right now?

test_verify_one_file! {
    #[ignore] #[test] test_recommends verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        spec fn foo(x: u8)
            recommends x > 10,
        {
            true
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
                foo(x), // should be a recommends failure
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "recommends failure")
}

// If you wrongly try to apply a mode

test_verify_one_file! {
    #[ignore] #[test] test_proxy_marked_spec verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[spec]
        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` cannot be marked `spec`")
}

test_verify_one_file! {
    #[ignore] #[test] test_proxy_marked_proof verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[proof]
        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` cannot be marked `proof`")
}
