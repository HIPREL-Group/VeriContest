use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_fold(s: Seq<i32>) -> i32
        decreases s.len(),
    {
        if s.len() == 0 {
            0i32
        } else {
            Self::xor_fold(s.drop_last()) ^ s.last()
        }
    }

    pub open spec fn and_xor_fold(a: i32, s: Seq<i32>) -> i32
        decreases s.len(),
    {
        if s.len() == 0 {
            0i32
        } else {
            Self::and_xor_fold(a, s.drop_last()) ^ (a & s.last())
        }
    }

    pub open spec fn all_pairs_xor(s1: Seq<i32>, s2: Seq<i32>) -> i32
        decreases s1.len(),
    {
        if s1.len() == 0 {
            0i32
        } else {
            Self::all_pairs_xor(s1.drop_last(), s2) ^ Self::and_xor_fold(s1.last(), s2)
        }
    }

    proof fn lemma_and_zero(a: i32)
        ensures a & 0i32 == 0i32,
    {
        assert(a & 0i32 == 0i32) by(bit_vector);
    }

    proof fn lemma_zero_and(a: i32)
        ensures 0i32 & a == 0i32,
    {
        assert(0i32 & a == 0i32) by(bit_vector);
    }

    proof fn lemma_and_distributes_over_xor(a: i32, b: i32, c: i32)
        ensures a & (b ^ c) == (a & b) ^ (a & c),
    {
        assert(a & (b ^ c) == (a & b) ^ (a & c)) by(bit_vector);
    }

    proof fn lemma_factor_and(a: i32, b: i32, c: i32)
        ensures (a & c) ^ (b & c) == (a ^ b) & c,
    {
        assert((a & c) ^ (b & c) == (a ^ b) & c) by(bit_vector);
    }

    proof fn lemma_and_xor_fold_equals(a: i32, s: Seq<i32>)
        ensures Self::and_xor_fold(a, s) == a & Self::xor_fold(s),
        decreases s.len(),
    {
        if s.len() == 0 {
            Self::lemma_and_zero(a);
        } else {
            Self::lemma_and_xor_fold_equals(a, s.drop_last());
            Self::lemma_and_distributes_over_xor(a, Self::xor_fold(s.drop_last()), s.last());
        }
    }

    proof fn lemma_all_pairs_xor_equals(s1: Seq<i32>, s2: Seq<i32>)
        ensures Self::all_pairs_xor(s1, s2) == Self::xor_fold(s1) & Self::xor_fold(s2),
        decreases s1.len(),
    {
        if s1.len() == 0 {
            Self::lemma_zero_and(Self::xor_fold(s2));
        } else {
            Self::lemma_all_pairs_xor_equals(s1.drop_last(), s2);
            Self::lemma_and_xor_fold_equals(s1.last(), s2);
            Self::lemma_factor_and(
                Self::xor_fold(s1.drop_last()),
                s1.last(),
                Self::xor_fold(s2),
            );
        }
    }

    pub fn get_xor_sum(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: i32)
        requires
            1 <= arr1.len() <= 100_000,
            1 <= arr2.len() <= 100_000,
            forall |i: int| 0 <= i < arr1.len() ==> 0 <= #[trigger] arr1[i] <= 1_000_000_000,
            forall |j: int| 0 <= j < arr2.len() ==> 0 <= #[trigger] arr2[j] <= 1_000_000_000,
        ensures
            result == Self::all_pairs_xor(arr1@, arr2@),
    {
        let mut xor1: i32 = 0;
        let mut i: usize = 0;
        while i < arr1.len()
            invariant
                0 <= i <= arr1.len(),
                xor1 == Self::xor_fold(arr1@.take(i as int)),
            decreases arr1.len() - i,
        {
            proof {
                assert(arr1@.take(i as int + 1).drop_last() =~= arr1@.take(i as int));
            }
            xor1 = xor1 ^ arr1[i];
            i += 1;
        }
        let mut xor2: i32 = 0;
        let mut j: usize = 0;
        while j < arr2.len()
            invariant
                0 <= j <= arr2.len(),
                xor2 == Self::xor_fold(arr2@.take(j as int)),
            decreases arr2.len() - j,
        {
            proof {
                assert(arr2@.take(j as int + 1).drop_last() =~= arr2@.take(j as int));
            }
            xor2 = xor2 ^ arr2[j];
            j += 1;
        }
        proof {
            assert(arr1@.take(arr1@.len() as int) =~= arr1@);
            assert(arr2@.take(arr2@.len() as int) =~= arr2@);
            Self::lemma_all_pairs_xor_equals(arr1@, arr2@);
        }
        xor1 & xor2
    }
}

}
