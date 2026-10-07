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
    pub open spec fn is_intersection(seq1: Seq<i32>, seq2: Seq<i32>, res: Seq<i32>) -> bool 
    {
        (forall |x: i32| #[trigger] res.contains(x) ==> seq1.contains(x) && seq2.contains(x)) &&
        (forall |x: i32| (#[trigger] seq1.contains(x) && seq2.contains(x)) ==> res.contains(x)) &&
        Solution::no_duplicates(res)
    }

    pub fn intersection(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
        ensures
            Solution::is_intersection(nums1@, nums2@, result@),
    {

    }
}

} 
