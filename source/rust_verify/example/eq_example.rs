#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus!{

#[verifier::external_type_specification]
pub struct ExOrdering(std::cmp::Ordering);

// Pretend this is std::cmp::PartialEq

trait PartialEq {
    fn eq(&self, other: &Self) -> bool;
    fn ne(&self, other: &Self) -> bool;
}

// This trait will be defined in vstd:

trait VEq : PartialEq {
    spec fn rel(&self, other: &Self) -> bool;

    // Proof that rel is an equivalence relation

    proof fn reflexive(a: &Self)
        ensures a.rel(a);

    proof fn symmetric(a: &Self, b: &Self)
        ensures a.rel(b) ==> b.rel(a);

    proof fn transitive(a: &Self, b: &Self, c: &Self)
        requires a.rel(b), b.rel(c)
        ensures a.rel(c);

    // Proof that `eq` and `ne` return the value of `rel`:

    proof fn fns_correct(a: &Self, b: &Self)
        ensures
            // call_ensures is a verus builtin that means
            // "this is a valid input-output pair for the function Self::eq"
            call_ensures(Self::eq, (a, b), true) ==> a.rel(b),
            call_ensures(Self::eq, (a, b), false) ==> !a.rel(b),

            call_ensures(Self::ne, (a, b), true) ==> !a.rel(b),
            call_ensures(Self::ne, (a, b), false) ==> a.rel(b);
}

// Example usage

struct Mod2 { u: u64 }

impl Mod2 {
    spec fn view(&self) -> int {
        (self.u % 2) as int
    }
}

impl PartialEq for Mod2 {
    fn eq(&self, other: &Self) -> (b: bool)
        ensures b == (self@ == other@),
    {
        self.u % 2 == other.u % 2
    }

    fn ne(&self, other: &Self) -> (b: bool)
        ensures b == (self@ != other@),
    {
        self.u % 2 != other.u % 2
    }
}

impl VEq for Mod2 {
    spec fn rel(&self, other: &Self) -> bool {
        self@ == other@
    }

    // Proof that rel is an equivalence relation

    proof fn reflexive(a: &Self)
    { }

    proof fn symmetric(a: &Self, b: &Self)
    { }

    proof fn transitive(a: &Self, b: &Self, c: &Self)
    { }

    // Proof that `eq` and `ne` return the value of `rel`:

    proof fn fns_correct(a: &Self, b: &Self)
    { }
}

fn main() { }

}
