#![allow(unused_imports)]

// ANCHOR: full
use crate::prelude::*;

verus!{

// Module to keep Dupe definitions private
mod DupeMod {
    use crate::prelude::*;
    use state_machines_macros::*;

    use crate as vstd; // necessary to use tokenized_state_machine in vstd

    tokenized_state_machine!(Dupe<T> {
        fields {
            #[sharding(storage_option)]
            pub storage: Option<T>,

            #[sharding(constant)]
            pub val: T,
        }

        init!{
            initialize_one(t: T) {
                // Initialize with a single reader
                init storage = Option::Some(t);
                init val = t;
            }
        }

        #[invariant]
        pub fn agreement(&self) -> bool {
            self.storage == Option::Some(self.val)
        }

        property!{
            borrow() {
                guard storage >= Some(pre.val);
            }
        }

         #[inductive(initialize_one)]
         fn initialize_one_inductive(post: Self, t: T) { }
    });
}

use DupeMod::*;

/// Allows shared access to any (tracked) ghost resource, making it
/// read-only "forever".
///
/// This is sort of the like "the `Rc` of ghost objects".
/// There's no actual reference counter (since it's a ghost object
/// and is never garbage-collected) but it has the same API:
/// It is cloneable, and the contents are borrowable read-only.

// TODO make it Copy

pub tracked struct Shareable<T> {
    tracked inst: Dupe::Instance<T>,
}

impl<T> Shareable<T> {
    pub closed spec fn wf(self) -> bool {
        true
    }

    pub closed spec fn view(self) -> T {
        self.inst.val()
    }

    pub proof fn new(tracked t: T) -> (tracked s: Self)
        ensures s.wf() && s@ == t,
    {
        let tracked inst = Dupe::Instance::initialize_one(/* spec */ t, Option::Some(t));
        Shareable {
            inst,
        }
    }

    pub proof fn clone(tracked &self) -> (tracked other: Self)
        requires self.wf(),
        ensures other.wf() && self@ == other@,
    {
        Shareable { inst: self.inst.clone() }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires self.wf(),
        ensures *t == self@,
    {
        self.inst.borrow()
    }
}

}
