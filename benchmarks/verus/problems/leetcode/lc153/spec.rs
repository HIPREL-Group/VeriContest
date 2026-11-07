use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_rotation_point(nums: Seq<i32>, k: int) -> bool {
        0 <= k < nums.len()
        && (forall |a: int, b: int| k <= a < b < nums.len() ==> nums[a] < nums[b])
        && (forall |a: int, b: int| 0 <= a < b < k ==> nums[a] < nums[b])
        && (k == 0 || forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() ==> nums[a] > nums[b])
    }

    pub fn find_min(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 5000,
            forall |i: int| 0 <= i < nums.len() ==> -5000 <= #[trigger] nums[i] <= 5000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
            exists |k: int| Self::is_rotation_point(nums@, k),
        ensures
            forall |i: int| 0 <= i < nums.len() ==> result <= nums[i],
            exists |i: int| 0 <= i < nums.len() && result == nums[i],
    {
    }
}

}
