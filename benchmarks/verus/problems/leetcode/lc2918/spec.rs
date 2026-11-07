use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adjusted(x: int) -> int {
        if x == 0 { 1 } else { x }
    }

    pub open spec fn prefix_min_sum(nums: Seq<i32>, upto: nat) -> int
        recommends
            upto <= nums.len(),
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::prefix_min_sum(nums, (upto - 1) as nat) + Self::adjusted(nums[(upto - 1) as int] as int)
        }
    }

    pub open spec fn prefix_zero_count(nums: Seq<i32>, upto: nat) -> int
        recommends
            upto <= nums.len(),
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::prefix_zero_count(nums, (upto - 1) as nat)
                + if nums[(upto - 1) as int] == 0 { 1int } else { 0int }
        }
    }

    pub open spec fn min_equal_spec(nums1: Seq<i32>, nums2: Seq<i32>) -> int {
        let s1 = Self::prefix_min_sum(nums1, nums1.len() as nat);
        let s2 = Self::prefix_min_sum(nums2, nums2.len() as nat);
        let z1 = Self::prefix_zero_count(nums1, nums1.len() as nat);
        let z2 = Self::prefix_zero_count(nums2, nums2.len() as nat);
        if s1 < s2 && z1 == 0 {
            -1
        } else if s2 < s1 && z2 == 0 {
            -1
        } else if s1 >= s2 {
            s1
        } else {
            s2
        }
    }

    pub fn min_sum(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i64)
        requires
            1 <= nums1.len() <= 100000,
            1 <= nums2.len() <= 100000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000000,
        ensures
            result as int == Self::min_equal_spec(nums1@, nums2@),
    {
    }
}

}
