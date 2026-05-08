use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_common(nums1: Vec<i32>, nums2: Vec<i32>) -> (res: i32)
        requires
            1 <= nums1.len() <= 100_000,
            1 <= nums2.len() <= 100_000,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i < j < nums1.len() ==> nums1[i] <= nums1[j],
            forall |i: int, j: int| 0 <= i < j < nums2.len() ==> nums2[i] <= nums2[j],
        ensures
            res == -1 <==> forall |x: i32| #[trigger] nums1@.contains(x) ==> !nums2@.contains(x),
            res != -1 ==> nums1@.contains(res) && nums2@.contains(res),
            res != -1 ==> forall |x: i32| nums1@.contains(x) && nums2@.contains(x) ==> res <= x,
    {
    }
}

}
