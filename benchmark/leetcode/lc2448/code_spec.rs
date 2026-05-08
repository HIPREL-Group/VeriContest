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

    pub open spec fn total_weight(cost: Seq<i32>, n: int) -> int
        recommends
            0 <= n && n <= cost.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::total_weight(cost, n - 1) + cost[n - 1] as int
        }
    }

    pub open spec fn bucket_weight(nums: Seq<i32>, cost: Seq<i32>, value: int, n: int) -> int
        recommends
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::bucket_weight(nums, cost, value, n - 1)
                + if nums[n - 1] as int == value { cost[n - 1] as int } else { 0 }
        }
    }

    pub open spec fn prefix_weight(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int) -> int
        recommends
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::prefix_weight(nums, cost, target, n - 1)
                + if nums[n - 1] as int <= target { cost[n - 1] as int } else { 0 }
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
        let max_value: usize = 1_000_000;
        let n = nums.len();
        let mut weights: Vec<i64> = Vec::new();
        let mut zeroes: usize = 0;

        while zeroes < max_value + 1 {
            weights.push(0);
            zeroes = zeroes + 1;
        }

        let mut total_weight: i64 = 0;
        let mut current: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let value = nums[i] as usize;
            let c = cost[i] as i64;
            weights.set(value, weights[value] + c);
            total_weight = total_weight + c;
            current = current + (nums[i] as i64 - 1) * c;
            i = i + 1;
        }

        let mut target: usize = 1;
        let mut prefix: i64 = weights[1];
        let mut best: i64 = current;
        while target < max_value {
            let delta = prefix - (total_weight - prefix);
            current = current + delta;
            target = target + 1;
            prefix = prefix + weights[target];
            if current < best {
                best = current;
            }
        }

        best
    }
}

}
