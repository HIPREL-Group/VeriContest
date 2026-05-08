use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn nat_min(a: nat, b: nat) -> nat {
        if a <= b { a } else { b }
    }

    pub open spec fn count_occ_prefix(s: Seq<i32>, n: nat, v: i32) -> nat
        recommends
            n <= s.len(),
        decreases n
    {
        if n == 0 {
            0nat
        } else {
            Solution::count_occ_prefix(s, (n - 1) as nat, v) + if s[(n - 1) as int] == v { 1nat } else { 0nat }
        }
    }

    pub open spec fn count_occ(s: Seq<i32>, v: i32) -> nat {
        Solution::count_occ_prefix(s, s.len() as nat, v)
    }

    pub fn intersect(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
        ensures
            forall |v: int| 0 <= v <= 1000 ==> #[trigger] Solution::count_occ(result@, v as i32)
                == Solution::nat_min(Solution::count_occ(nums1@, v as i32), Solution::count_occ(nums2@, v as i32)),
            forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
    {
    }
}

}
