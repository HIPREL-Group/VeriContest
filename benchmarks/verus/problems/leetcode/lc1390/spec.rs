use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn div_count_from(n: int, d: int) -> int
        decreases n - d + 1
    {
        if d <= 0 || d > n { 0 }
        else if n % d == 0 { 1 + Self::div_count_from(n, d + 1) }
        else { Self::div_count_from(n, d + 1) }
    }

    pub open spec fn div_sum_from(n: int, d: int) -> int
        decreases n - d + 1
    {
        if d <= 0 || d > n { 0 }
        else if n % d == 0 { d + Self::div_sum_from(n, d + 1) }
        else { Self::div_sum_from(n, d + 1) }
    }

    pub open spec fn four_div_sum(nums: Seq<i32>, i: int) -> int
        decreases nums.len() - i
    {
        if i < 0 || i >= nums.len() { 0 }
        else if Self::div_count_from(nums[i] as int, 1) == 4 {
            Self::div_sum_from(nums[i] as int, 1) + Self::four_div_sum(nums, i + 1)
        }
        else { Self::four_div_sum(nums, i + 1) }
    }

    pub fn sum_four_divisors(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            0 <= Self::four_div_sum(nums@, 0) <= i32::MAX as int,
        ensures
            result as int == Self::four_div_sum(nums@, 0),
    {
    }
}

}
