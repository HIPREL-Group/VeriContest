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
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len()
        {
            let n = nums[i];
            let term: i64 = (n as i64 + divisor as i64 - 1) / divisor as i64;
            sum += term;
            i += 1;
        }
        sum
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
        let mut left: i32 = 1;
        let mut right: i32 = 1_000_000;

        while left < right
        {
            let mid = left + (right - left) / 2;
            let sum = Self::sum_with_divisor(&nums, mid);
            if sum <= threshold as i64 {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        left
    }
}

}
