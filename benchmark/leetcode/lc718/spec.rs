use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn common_at(a: Seq<i32>, b: Seq<i32>, i: int, j: int, L: int) -> bool {
        0 <= i && i + L <= a.len()
        && 0 <= j && j + L <= b.len()
        && forall |k: int| 0 <= k < L ==> (#[trigger] a[i + k]) == b[j + k]
    }

    pub fn find_length(nums1: Vec<i32>, nums2: Vec<i32>) -> (res: i32)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            (nums1.len() + 1) * (nums2.len() + 1) <= usize::MAX,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 100,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 100,
        ensures
            res >= 0,
            res <= (nums1.len() as int) && res <= (nums2.len() as int),
            exists |i: int, j: int| Self::common_at(nums1@, nums2@, i, j, res as int),
            forall |L: int, i: int, j: int|
                (L > res as int && (#[trigger] Self::common_at(nums1@, nums2@, i, j, L))) ==> false,
    {
    }
}

}
