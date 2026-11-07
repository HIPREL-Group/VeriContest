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

    pub fn get_xor_sum(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: i32)
        requires
            1 <= arr1.len() <= 100_000,
            1 <= arr2.len() <= 100_000,
            forall |i: int| 0 <= i < arr1.len() ==> 0 <= #[trigger] arr1[i] <= 1_000_000_000,
            forall |j: int| 0 <= j < arr2.len() ==> 0 <= #[trigger] arr2[j] <= 1_000_000_000,
        ensures
            result == Self::all_pairs_xor(arr1@, arr2@),
    {
    }
}

}
