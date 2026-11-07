use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div(x: int, d: int) -> int {
        (x + d - 1) / d
    }

    pub open spec fn sum_prefix(nums: Seq<i32>, d: int, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::sum_prefix(nums, d, n - 1) + Self::ceil_div(nums[n - 1] as int, d)
        }
    }

    pub open spec fn sum_by_divisor(nums: Seq<i32>, d: int) -> int {
        Self::sum_prefix(nums, d, nums.len() as int)
    }

    fn sum_with_divisor(nums: &Vec<i32>, divisor: i32) -> (sum: i64)
        requires
            1 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
            1 <= divisor <= 1_000_000,
        ensures
            sum as int == Self::sum_by_divisor(nums@, divisor as int),
            0 <= sum <= 50_000 * 1_000_000,
    {
        
    }

    pub fn smallest_divisor(nums: Vec<i32>, threshold: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
            nums.len() <= threshold <= 1_000_000,
        ensures
            1 <= res <= 1_000_000,
            Self::sum_by_divisor(nums@, res as int) <= threshold as int,
            forall |d: int| 1 <= d < res ==> #[trigger] Self::sum_by_divisor(nums@, d) > threshold as int,
    {
        
    }
}

}
