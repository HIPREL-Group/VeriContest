use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn no_duplicates(s: Seq<i32>) -> bool
    {
        forall |i: int, j: int|
            0 <= i < s.len() && 0 <= j < s.len() && i != j
            ==> s[i] != s[j]
    }

    pub open spec fn is_difference(nums1: Seq<i32>, nums2: Seq<i32>, result: Seq<Seq<i32>>) -> bool
    {
        result.len() == 2 &&
        (forall |x: i32| #[trigger] result[0].contains(x) ==> nums1.contains(x) && !nums2.contains(x)) &&
        (forall |x: i32| (#[trigger] nums1.contains(x) && !#[trigger] nums2.contains(x)) ==> result[0].contains(x)) &&
        Solution::no_duplicates(result[0]) &&
        (forall |x: i32| #[trigger] result[1].contains(x) ==> nums2.contains(x) && !nums1.contains(x)) &&
        (forall |x: i32| (#[trigger] nums2.contains(x) && !#[trigger] nums1.contains(x)) ==> result[1].contains(x)) &&
        Solution::no_duplicates(result[1])
    }

    pub fn find_difference(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<Vec<i32>>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> -1000 <= #[trigger] nums1[i] <= 1000,
            forall |j: int| 0 <= j < nums2.len() ==> -1000 <= #[trigger] nums2[j] <= 1000,
        ensures
            result.len() == 2,
            Solution::is_difference(nums1@, nums2@, seq![result[0]@, result[1]@]),
    {

    }
}

}
