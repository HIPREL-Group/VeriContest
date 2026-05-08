use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn search_range(nums: Vec<i32>, target: i32) -> (result: Vec<i32>)
        requires
            0 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
            -1_000_000_000 <= target <= 1_000_000_000,
        ensures
            result.len() == 2,
            result[0] == -1i32 || result[0] >= 0,
            result[1] == -1i32 || result[1] >= 0,
            (forall |i: int| 0 <= i < nums.len() ==> nums[i] != target) ==> (result[0] == -1i32 && result[1] == -1i32),
            (result[0] == -1i32) ==> (forall |i: int| 0 <= i < nums.len() ==> nums[i] != target),
            result[0] >= 0 ==> (
                0 <= result[0] < nums.len() as i32
                && nums[result[0] as int] == target
                && (result[0] == 0i32 || nums[result[0] as int - 1] < target)
            ),
            result[1] >= 0 ==> (
                0 <= result[1] < nums.len() as i32
                && nums[result[1] as int] == target
                && (result[1] == nums.len() as i32 - 1 || nums[result[1] as int + 1] > target)
            ),
            (result[0] == -1i32) == (result[1] == -1i32),
            result[0] >= 0 ==> result[0] <= result[1],
    {
    }
}

}
