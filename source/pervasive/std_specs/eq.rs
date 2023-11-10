use crate::prelude::*;

crate::prelude::verus! {

#[verifier::external_fn_specification]
pub fn ex_partial_eq<T: PartialEq<T> + Eq + crate::prelude::View, Rhs: ?Sized>(t: &T, other: &T) -> (res: bool)
    ensures
        /* T: EqIsViewEq ==> */ (t@ == other@) == res
{
    t.eq(other)
}

}