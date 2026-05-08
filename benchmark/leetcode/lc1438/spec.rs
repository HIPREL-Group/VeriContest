use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_ok(nums: Seq<i32>, limit: int, l: int, r: int) -> bool {
        &&& 0 <= l < r <= nums.len()
        &&& forall |i: int, j: int| l <= i < r && l <= j < r ==> (nums[i] as int - nums[j] as int) <= limit
    }

    pub fn longest_subarray(nums: Vec<i32>, limit: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            0 <= limit <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= result <= nums.len() as i32,
            exists |l: int, r: int| Self::window_ok(nums@, limit as int, l, r) && result as int == r - l,
            forall |l: int, r: int| Self::window_ok(nums@, limit as int, l, r) ==> r - l <= result as int,
    {
    }
}

}