use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seen_in_suffix(nums: Seq<i32>, v: int, ops: int) -> bool {
        exists |q: int|
            0 <= q < ops
            && 0 <= nums.len() - ops + q < nums.len()
            && #[trigger] nums[nums.len() - ops + q] == v
    }

    pub open spec fn all_seen(nums: Seq<i32>, k: int, ops: int) -> bool {
        forall |v: int| 1 <= v <= k ==> Self::seen_in_suffix(nums, v, ops)
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            1 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
            Self::all_seen(nums@, k as int, nums.len() as int),
        ensures
            1 <= result <= nums.len(),
            Self::all_seen(nums@, k as int, result as int),
            forall |t: int| 1 <= t < result ==> !Self::all_seen(nums@, k as int, t),
    {
    }
}

}
