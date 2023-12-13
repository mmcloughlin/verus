#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] basic_test ["vstd"] => verus_code! {
        fn llama(x: u8) -> (b: bool)
            requires x == 4 || x == 7,
            ensures b == (x == 4)
        {
            x == 4
        }

        fn test() {
            let t = llama;

            let b = t(4);
            assert(b);

            let b = t(7);
            assert(!b);

            assert(forall |x| (x == 4 || x == 7) ==> call_requires(llama, (x,)));
            assert(forall |x, y| call_ensures(llama, (x,), y) ==> x == 4 ==> y);
            assert(forall |x, y| call_ensures(llama, (x,), y) ==> x == 7 ==> !y);
        }

        fn test2() {
            let t = llama;

            let b = t(4);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = llama;

            t(12); // FAILS
        }

        fn test4() {
            assert(forall |x| (x == 5) ==> call_requires(llama, (x,))); // FAILS
        }

        fn test5() {
            assert(forall |x, y| call_ensures(llama, (x,), y) ==> x == 4 ==> !y); // FAILS
        }

        fn takes_fn1<F: Fn(u8) -> bool>(f: F)
            requires
                call_requires(f, (4,)),
                call_requires(f, (7,)),
                forall |x, y| call_ensures(f, (x,), y) ==> x == 4 ==> y
        {
        }

        fn test_take1() {
            takes_fn1(llama);
        }

        fn takes_fn2<F: Fn(u8) -> bool>(f: F)
            requires
                call_requires(f, (6,)),
        {
        }

        fn test_take2() {
            takes_fn2(llama); // FAILS
        }

        fn takes_fn3<F: Fn(u8) -> bool>(f: F)
            requires
                forall |x, y| call_ensures(f, (x,), y) ==> x == 7 ==> y
        {
        }

        fn test_take3() {
            takes_fn3(llama); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] generics_test ["vstd"] => verus_code! {
        fn llama<T>(x: T, y: T, z: T) -> (b: bool)
            requires x == y,
            ensures b == (y == z),
        {
            // We can't actually implement this, but it doesn't matter for the test
            assume(false);
            true
        }

        fn test() {
            let t = llama;

            let b = t(4, 4, 6);
            assert(!b);

            let b = t(4, 4, 4);
            assert(b);

            assert(forall |x: u8, y: u8, z: u8| (x == y) ==> call_requires(llama, (x,y,z)));
            assert(forall |x: u8, y: u8, z: u8, b| call_ensures(llama, (x,y,z),b) ==> b == (y == z));
        }

        fn test2() {
            let t = llama;

            let b = t(4, 4, 4);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = llama;

            t(12, 13, 14); // FAILS
        }

        fn test4() {
            assert(forall |x: u8, y: u8, z: u8| (y == z) ==> call_requires(llama, (x,y,z))); // FAILS
        }

        fn test5() {
            assert(forall |x: u8, y: u8, z: u8, b| call_ensures(llama, (x,y,z),b) ==> b == (y != z)); // FAILS
        }

        struct X { x: u8 }

        fn takes_fn1<F: Fn(X, X, X) -> bool>(f: F)
            requires
                call_requires(f, (X { x: 4 }, X { x: 4 } , X { x: 4 })),
                call_requires(f, (X { x: 7 }, X { x: 7 } , X { x: 4 })),
                forall |x: X, y: X, z: X, b| call_ensures(f, (x,y,z), b) ==> b == (y == z)
        {
        }

        fn test_take1() {
            takes_fn1(llama);
        }

        fn takes_fn2<F: Fn(u8, u8, u8) -> bool>(f: F)
            requires
                call_requires(f, (6,7,8)),
        {
        }

        fn test_take2() {
            takes_fn2(llama); // FAILS
        }

        fn takes_fn3<F: Fn(u8, u8, u8) -> bool>(f: F)
            requires
                forall |x: u8, y: u8, z: u8, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take3() {
            takes_fn3(llama); // FAILS
        }

        fn takes_fn4<T, F: Fn(T, T, T) -> bool>(f: F)
            requires
                forall |x: T, y: T, z: T, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take4() {
            takes_fn4(llama::<u8>); // FAILS
        }

    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file_with_options! {
    #[test] with_trait ["vstd"] => verus_code! {
        trait Tr : Sized {
            fn llama(self, y: Self, z: Self) -> (b: bool)
                requires self == y,
                ensures b == (y == z);
        }

        struct X {
            t: u8,
        }

        impl Tr for X {
            fn llama(self, y: Self, z: Self) -> (b: bool)
            {
                assume(false);
                true
            }
        }

        fn test() {
            let t = <X as Tr>::llama;

            let x = X { t: 4 };
            let y = X { t: 4 };
            let z = X { t: 6 };

            let b = t(x, y, z);
            assert(!b);

            let x = X { t: 4 };
            let y = X { t: 4 };
            let z = X { t: 4 };

            let b = t(x, y, z);
            assert(b);

            assert(forall |x: X, y: X, z: X| (x == y) ==> call_requires(X::llama, (x,y,z)));
            assert(forall |x: X, y: X, z: X, b| call_ensures(X::llama, (x,y,z),b) ==> b == (y == z));
        }

        fn test2() {
            let t = <X as Tr>::llama;

            let x = X { t: 4 };
            let y = X { t: 4 };
            let z = X { t: 4 };

            let b = t(x, y, z);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = <X as Tr>::llama;

            let x = X { t: 12 };
            let y = X { t: 13 };
            let z = X { t: 14 };

            t(x, y, z); // FAILS
        }

        fn test4() {
            assert(forall |x: X, y: X, z: X| (y == z) ==> call_requires(X::llama, (x,y,z))); // FAILS
        }

        fn test5() {
            assert(forall |x: X, y: X, z: X, b| call_ensures(X::llama, (x,y,z),b) ==> b == (y != z)); // FAILS
        }

        fn takes_fn1<F: Fn(X, X, X) -> bool>(f: F)
            requires
                call_requires(f, (X { t: 4 }, X { t: 4 } , X { t: 4 })),
                call_requires(f, (X { t: 7 }, X { t: 7 } , X { t: 4 })),
                forall |x: X, y: X, z: X, b| call_ensures(f, (x,y,z), b) ==> b == (y == z)
        {
        }

        fn test_take1() {
            takes_fn1(X::llama);
        }

        fn takes_fn2<F: Fn(X, X, X) -> bool>(f: F)
            requires
                call_requires(f, (X { t: 6 }, X { t: 7 }, X { t: 8 })),
        {
        }

        fn test_take2() {
            takes_fn2(X::llama); // FAILS
        }

        fn takes_fn3<F: Fn(X, X, X) -> bool>(f: F)
            requires
                forall |x: X, y: X, z: X, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take3() {
            takes_fn3(X::llama); // FAILS
        }

        fn takes_fn4<T, F: Fn(T, T, T) -> bool>(f: F)
            requires
                forall |x: T, y: T, z: T, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take4() {
            takes_fn4(X::llama); // FAILS
        }
    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file! {
    #[test] spec_fn_error verus_code! {
        spec fn foo() -> bool { true }

        fn test() {
            let x = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file! {
    #[test] proof_fn_error verus_code! {
        proof fn foo() -> bool { true }

        fn test() {
            let x = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file! {
    #[test] mut_params_error verus_code! {
        fn stuff(x: &mut u8) { }

        fn test() {
            let x = stuff;
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: using a function that takes '&mut' params as a value")
}

test_verify_one_file! {
    #[test] recursion1 verus_code! {
        fn test(x: u8)
            requires call_requires(test, (x,)),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion2 verus_code! {
        spec fn s(x: u8) -> bool {
            call_requires(test, (x,))
        }

        fn test(x: u8)
            requires s(x),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion3 verus_code! {
        spec fn s(x: u8) -> bool {
            call_requires(test, (x,))
        }

        fn test(x: u8)
            ensures s(x),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion4 verus_code! {
        spec fn s(x: u8) -> bool {
            call_ensures(test, (x,), ())
        }

        fn test(x: u8)
            requires s(x),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion5_okay verus_code! {
        // This is ok because we're only referencing the *type* FnDef(test),
        // but not the 'requires' or 'ensures',
        // which is just a singleton.
        fn test(x: u8)
            requires test == test,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] recursion6_via_call_requires verus_code! {
        spec fn foo<F: FnOnce(u8) -> bool>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8) -> bool
            requires foo(test)
        {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion7_via_call_requires verus_code! {
        spec fn foo<F: FnOnce(u8) -> bool>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8) -> bool
            requires foo(test)
        {
            false
        }

        // Not supported currently, but if it were, this would need to be a recursion error
    } => Err(err) => assert_vir_error_msg(err, "Verus does yet not support this type of bound")
}

test_verify_one_file! {
    #[test] recursion8_via_fn_once verus_code! {
        spec fn foo<F: FnOnce(u8)>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion9_via_fn verus_code! {
        spec fn foo<F: Fn(u8)>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion10_via_fn_mut verus_code! {
        spec fn foo<F: FnMut(u8)>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion11_via_trait_impl_in_function_generics verus_code! {
        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        trait Qr {
        }

        impl<T> Tr for T
          where T: Qr
        {
            // cyclic dependency with alpaca
            spec fn stuff(&self) -> bool {
                alpaca(*self)
            }
        }

        spec fn alpaca<T: Qr>(qr: T) -> bool {
            // depends on the bound `T: Tr`
            // which depends on the implementation `T: Qr --> T: Tr`
            // which in turn depends on `alpaca`
            call_requires(test::<T>, (0,))
        }

        // The definition of `test` itself is fine
        fn test<T: Tr>(x: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "self-reference in a trait definition")
}

test_verify_one_file! {
    #[test] recursion12_via_trait_impl_in_function_generics verus_code! {
        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        struct X { }

        impl Tr for X
        {
            // cyclic dependency with alpaca
            spec fn stuff(&self) -> bool {
                alpaca()
            }
        }

        spec fn alpaca() -> bool {
            // depends on the bound `X: Tr`
            // which depends on the above trait impl
            // which in turn depends on `alpaca`
            call_ensures(test::<X>, (0,), ())
        }

        // The definition of `test` itself is fine
        fn test<T: Tr>(x: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "self-reference in a trait definition")
}

test_verify_one_file! {
    #[test] recursion13_via_fn_with_requires_ensures verus_code! {
        use vstd::prelude::*;

        spec fn foo<F: FnWithRequiresEnsures<(u8,), ()>>(f: F) -> bool {
            f.requires((0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of this function")
}

test_verify_one_file! {
    #[test] recursion14_via_fn_with_requires_ensures verus_code! {
        use vstd::prelude::*;

        spec fn foo<F: FnWithRequiresEnsures<(u8,), ()>>(f: F) -> bool {
            f.requires((0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }

        // Not supported currently, but if it were, this would need to be a recursion error
    } => Err(err) => assert_vir_error_msg(err, "Verus does yet not support this type of bound")
}

test_verify_one_file! {
    #[test] recursion15_via_trait_impl_in_function_generics_fn_with_requires_ensures verus_code! {
        use vstd::prelude::*;

        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        struct X { }

        impl Tr for X
        {
            // cyclic dependency with alpaca
            spec fn stuff(&self) -> bool {
                alpaca()
            }
        }

        spec fn alpaca() -> bool {
            // depends on the bound `X: Tr`
            // which depends on the above trait impl
            // which in turn depends on `alpaca`
            (test::<X>).requires((0,))
        }

        // The definition of `test` itself is fine
        fn test<T: Tr>(x: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "self-reference in a trait definition")
}
