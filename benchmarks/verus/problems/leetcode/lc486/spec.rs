use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn best(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn game_diff(nums: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i <= nums.len(),
            -1 <= j < nums.len(),
            i <= j + 1,
        decreases if i > j { 0int } else { j - i + 1 },
    {
        if i > j {
            0
        } else if i == j {
            nums[i] as int
        } else {
            Self::best(
                nums[i] as int - Self::game_diff(nums, i + 1, j),
                nums[j] as int - Self::game_diff(nums, i, j - 1),
            )
        }
    }

    pub fn predict_the_winner(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 20,
            forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 10_000_000,
        ensures
            result == (Self::game_diff(nums@, 0, nums.len() as int - 1) >= 0),
    {
    }
}

}
