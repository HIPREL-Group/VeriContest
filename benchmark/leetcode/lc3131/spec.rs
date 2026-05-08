use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn added_integer(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 100,
            nums1.len() == nums2.len(),
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> #[trigger] nums1[i] as int + (nums2[0] as int - nums1[0] as int) == nums2[i] as int,
        ensures
            forall |i: int| 0 <= i < nums1.len() ==> #[trigger] nums1[i] as int + result as int == nums2[i] as int,
    {
    }
}

}
