use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value_prefix(nums: Seq<i32>, end: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value_prefix(nums, end - 1, v)
                + if nums[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn count_value(nums: Seq<i32>, v: int) -> int {
        Self::count_value_prefix(nums, nums.len() as int, v)
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sum_smallest_from(nums: Seq<i32>, k: int, v: int) -> int
        decreases 101 - v,
    {
        if k <= 0 || v > 100 {
            0
        } else {
            let c = Self::count_value(nums, v);
            let t = Self::min_int(k, c);
            t * v + Self::sum_smallest_from(nums, k - t, v + 1)
        }
    }

    pub open spec fn sum_largest_from(nums: Seq<i32>, k: int, v: int) -> int
        decreases v,
    {
        if k <= 0 || v < 1 {
            0
        } else {
            let c = Self::count_value(nums, v);
            let t = Self::min_int(k, c);
            t * v + Self::sum_largest_from(nums, k - t, v - 1)
        }
    }

    pub open spec fn sum_smallest_k(nums: Seq<i32>, k: int) -> int {
        Self::sum_smallest_from(nums, k, 1)
    }

    pub open spec fn sum_largest_k(nums: Seq<i32>, k: int) -> int {
        Self::sum_largest_from(nums, k, 100)
    }

    pub open spec fn abs_int(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub fn abs_difference(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= nums.len(),
        ensures
            res as int == Self::abs_int(Self::sum_largest_k(nums@, k as int) - Self::sum_smallest_k(nums@, k as int)),
    {
        let n = nums.len();
        let mut freq: Vec<i64> = vec![0; 101];
        let mut i: usize = 0;
        while i < n {
            let idx = nums[i] as usize;
            freq.set(idx, freq[idx] + 1);
            i = i + 1;
        }

        let mut remaining_small: i64 = k as i64;
        let mut small_sum: i64 = 0;
        let mut value: usize = 1;
        while value <= 100 && remaining_small > 0 {
            let count_here = freq[value];
            let take = if remaining_small < count_here {
                remaining_small
            } else {
                count_here
            };
            small_sum = small_sum + take * value as i64;
            remaining_small = remaining_small - take;
            value = value + 1;
        }

        let mut remaining_large: i64 = k as i64;
        let mut large_sum: i64 = 0;
        let mut value_high: i32 = 100;
        while value_high >= 1 && remaining_large > 0 {
            let idx = value_high as usize;
            let count_here = freq[idx];
            let take = if remaining_large < count_here {
                remaining_large
            } else {
                count_here
            };
            large_sum = large_sum + take * value_high as i64;
            remaining_large = remaining_large - take;
            value_high = value_high - 1;
        }

        let diff = if large_sum >= small_sum {
            large_sum - small_sum
        } else {
            small_sum - large_sum
        };

        diff as i32
    }
}

} 
