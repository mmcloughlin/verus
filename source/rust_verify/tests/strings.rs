#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_pass_is_ascii verus_code! {
    #[allow(unused_imports)]
    use pervasive::string::*;

    fn str_is_ascii_passes() {
        let x = new_strlit("Hello World");
        proof {
            reveal_strlit("Hello World");
        }
        assert(x.is_ascii());
    }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_is_ascii verus_code! {
        use pervasive::string::*;
        fn str_is_ascii_fails() {
            let x = new_strlit("à");
            proof {
                reveal_strlit("à");
            }
            assert(x.is_ascii());
        }
    }   => Err(_)
}

test_verify_one_file! {
    #[test] test_pass_get_char verus_code! {
        use pervasive::string::*;
        fn get_char() {
            let x = new_strlit("hello world");
            proof {
                reveal_strlit("hello world");
            }
            assert(x@.len() == 11);
            let val = x.get_char(0);
            let h_u8 = 104;
            assert(h_u8 === val);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fail_get_char verus_code! {
        use pervasive::string::*;
        fn get_char_fails() {
            let x = new_strlit("hello world");
            let val = x.get_char(0);
            assert(val == 104);
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_passes_len verus_code! {
        use pervasive::string::*;

        pub fn len_passes() {
            let x = new_strlit("abcdef");
            proof {
                reveal_strlit("abcdef");
            }
            assert(x@.len() === 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_len verus_code! {
        use pervasive::string::*;

        pub fn len_fails() {
            let x = new_strlit("abcdef");
            proof {
                reveal_strlit("abcdef");
            }
            assert(x@.len() == 1);
        }
    } => Err(_)
}
