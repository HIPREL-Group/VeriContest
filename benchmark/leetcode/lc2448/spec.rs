use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn move_cost(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int) -> int
        recommends
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::move_cost(nums, cost, target, n - 1)
                + Self::abs_diff(nums[n - 1] as int, target) * cost[n - 1] as int
        }
    }

    pub fn min_cost(nums: Vec<i32>, cost: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() && nums.len() <= 100_000,
            nums.len() == cost.len(),
            forall|i: int| 0 <= i && i < nums.len() ==> 1 <= nums[i] && nums[i] <= 1_000_000,
            forall|i: int| 0 <= i && i < cost.len() ==> 1 <= cost[i] && cost[i] <= 1_000_000,
        ensures
            result >= 0,
            forall|target: int| 1 <= target && target <= 1_000_000 ==> result as int <= #[trigger] Self::move_cost(nums@, cost@, target, nums.len() as int),
            exists|target: int| 1 <= target && target <= 1_000_000 && result as int == Self::move_cost(nums@, cost@, target, nums.len() as int),
    {
    }
}

}
