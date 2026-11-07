use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inner_count(nums1: Seq<i32>, nums2: Seq<i32>, k: int, i: int, j: int) -> int
        decreases nums2.len() - j,
    {
        if j >= nums2.len() {
            0
        } else {
            (if nums1[i] as int % (nums2[j] as int * k) == 0 { 1int } else { 0int })
                + Self::inner_count(nums1, nums2, k, i, j + 1)
        }
    }

    pub open spec fn good_pair_count(nums1: Seq<i32>, nums2: Seq<i32>, k: int, i: int) -> int
        decreases nums1.len() - i,
    {
        if i >= nums1.len() {
            0
        } else {
            Self::inner_count(nums1, nums2, k, i, 0) + Self::good_pair_count(nums1, nums2, k, i + 1)
        }
    }

    pub fn number_of_pairs(nums1: Vec<i32>, nums2: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums1.len() <= 50,
            1 <= nums2.len() <= 50,
            forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 50,
            forall|j: int| 0 <= j < nums2.len() ==> 1 <= #[trigger] nums2[j] <= 50,
            1 <= k <= 50,
        ensures
            res as int == Self::good_pair_count(nums1@, nums2@, k as int, 0),
            0 <= res <= nums1.len() * nums2.len(),
    {
    }
}

}
