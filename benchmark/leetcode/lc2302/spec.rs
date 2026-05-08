use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn subarray_sum(nums: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            nums[start] as int + Self::subarray_sum(nums, start + 1, end)
        }
    }

    pub open spec fn score(nums: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
    {
        Self::subarray_sum(nums, start, end) * (end - start)
    }

    pub open spec fn first_valid_start(nums: Seq<i32>, k: int, start: int, end: int) -> int
        recommends
            0 <= start <= end <= nums.len(),
            1 <= k,
        decreases end - start,
    {
        if start >= end || Self::score(nums, start, end) < k {
            start
        } else {
            Self::first_valid_start(nums, k, start + 1, end)
        }
    }

    pub open spec fn end_count(nums: Seq<i32>, k: int, end: int) -> int
        recommends
            0 <= end <= nums.len(),
            1 <= k,
    {
        end - Self::first_valid_start(nums, k, 0, end)
    }

    pub open spec fn count_subarrays_prefix(nums: Seq<i32>, k: int, n: int) -> int
        recommends
            0 <= n <= nums.len(),
            1 <= k,
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_subarrays_prefix(nums, k, n - 1) + Self::end_count(nums, k, n)
        }
    }

    pub fn count_subarrays(nums: Vec<i32>, k: i64) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            1 <= k <= 1_000_000_000_000_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result >= 0,
            result as int == Self::count_subarrays_prefix(nums@, k as int, nums.len() as int),
    {
    }
}

}
