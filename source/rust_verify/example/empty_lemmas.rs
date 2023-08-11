use vstd::prelude::*;
use vstd::seq_lib::*;

verus!{

/// The concatenation of two subsequences derived from a non-empty sequence, 
/// the first obtained from skipping the last element, the second consisting only 
/// of the last element, is the original sequence.
pub proof fn lemma_add_last_back(self)
    requires 
        0 < self.len(),
    ensures
        #[trigger] self.drop_last().push(self.last()) =~= self,
{}

/// A sequence that is sliced at the pos-th element, concatenated 
/// with that same sequence sliced from the pos-th element, is equal to the 
/// original unsliced sequence.
pub proof fn lemma_split_at(self, pos: int)
    requires 
        0 <= pos <= self.len(),
    ensures 
        self.subrange(0,pos) + self.subrange(pos,self.len() as int) =~= self
{}

/// Any element in a slice is included in the original sequence.
pub proof fn lemma_element_from_slice(self, new: Seq<A>, a: int, b:int, pos: int)
    requires
        0 <= a <= b <= self.len(),
        new == self.subrange(a,b),
        a <= pos < b
    ensures
        pos - a < new.len(),
        new[pos-a] == self[pos],
{}

/// A slice (from s2..e2) of a slice (from s1..e1) of a sequence is equal to just a 
/// slice (s1+s2..s1+e2) of the original sequence.
pub proof fn lemma_slice_of_slice(self, s1: int, e1: int, s2: int, e2: int)
    requires 
        0 <= s1 <= e1 <= self.len(),
        0 <= s2 <= e2 <= e1 - s1,
    ensures
        self.subrange(s1,e1).subrange(s2,e2) =~= self.subrange(s1+s2,s1+e2),
{}

/// Unzipping a sequence of sequences and then zipping the resulting two sequences
/// back together results in the original sequence of sequences.
pub proof fn lemma_zip_of_unzip(self)
    ensures self.unzip().0.zip_with(self.unzip().1) =~= self,
{}

/// The last element of two concatenated sequences, the second one being non-empty, will be the 
/// last element of the latter sequence.
pub proof fn lemma_append_last<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        0 < s2.len(),
    ensures
        (s1 + s2).last() == s2.last(),
{}

/// The concatenation of sequences is associative
pub proof fn lemma_concat_associative<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
    ensures
        s1.add(s2.add(s3)) =~= s1.add(s2).add(s3),
{}

/// If sequences a and b don't have duplicates, and there are no 
/// elements in common between them, then the concatenated sequence 
/// a + b will not contain duplicates either.
pub proof fn lemma_no_dup_in_concat<A>(a: Seq<A>, b: Seq<A>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len()
            ==> a[i] != b[j]
    ensures
        #[trigger] (a+b).no_duplicates(),
{}

/// In a pre-ordered set, a greatest element is necessarily maximal.
pub proof fn lemma_greatest_implies_maximal(self, r: FnSpec(A,A) -> bool, max: A)
    requires pre_ordering(r),
    ensures is_greatest(r, max, self) ==> is_maximal(r, max, self),
{}

/// In a pre-ordered set, a least element is necessarily minimal.
pub proof fn lemma_least_implies_minimal(self, r: FnSpec(A,A) -> bool, min: A)
    requires pre_ordering(r),
    ensures is_least(r, min, self) ==> is_minimal(r, min, self),
{}


/// Removing a key from a map that previously contained that key decreases 
/// the map's length by one
pub proof fn lemma_remove_key_len(self, key: K)
    requires
        self.dom().contains(key),
        self.dom().finite(),
    ensures
        self.dom().len() == 1 + self.remove(key).dom().len(),
{}

/// The domain of a map after removing a key is equivalent to removing the key from 
/// the domain of the original map.
pub proof fn lemma_remove_equivalency(self, key: K)
    ensures
        self.remove(key).dom() == self.dom().remove(key),
{}   

} //verus!