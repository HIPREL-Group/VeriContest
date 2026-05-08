use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_range(x: int, min_k: int, max_k: int) -> bool {
        min_k <= x && x <= max_k
    }

    pub open spec fn last_bad(nums: Seq<i32>, min_k: int, max_k: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            -1
        } else if !Self::in_range(nums[n - 1] as int, min_k, max_k) {
            n - 1
        } else {
            Self::last_bad(nums, min_k, max_k, n - 1)
        }
    }

    pub open spec fn last_pos(nums: Seq<i32>, target: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            -1
        } else if nums[n - 1] as int == target {
            n - 1
        } else {
            Self::last_pos(nums, target, n - 1)
        }
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    pub open spec fn end_count(nums: Seq<i32>, min_k: int, max_k: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
    {
        if n <= 0 {
            0
        } else {
            let bad = Self::last_bad(nums, min_k, max_k, n);
            let bound = Self::min_int(
                Self::last_pos(nums, min_k, n),
                Self::last_pos(nums, max_k, n),
            );
            if bound > bad {
                bound - bad
            } else {
                0
            }
        }
    }

    pub open spec fn count_fixed_bound_subarrays(nums: Seq<i32>, min_k: int, max_k: int, n: int) -> int
        recommends
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_fixed_bound_subarrays(nums, min_k, max_k, n - 1)
                + Self::end_count(nums, min_k, max_k, n)
        }
    }

    pub fn count_subarrays(nums: Vec<i32>, min_k: i32, max_k: i32) -> (result: i64)
        requires
            2 <= nums.len() && nums.len() <= 100_000,
            1 <= min_k && min_k <= 1_000_000,
            1 <= max_k && max_k <= 1_000_000,
            forall|i: int| 0 <= i && i < nums.len() ==> 1 <= nums[i] && nums[i] <= 1_000_000,
        ensures
            result >= 0,
            result as int == Self::count_fixed_bound_subarrays(nums@, min_k as int, max_k as int, nums.len() as int),
    {
        let n = nums.len();
        let mut result: i64 = 0;
        let mut last_bad: i64 = -1;
        let mut last_min: i64 = -1;
        let mut last_max: i64 = -1;
        let mut i: usize = 0;

        while i < n {
            let value = nums[i];
            if value < min_k || value > max_k {
                last_bad = i as i64;
            }
            if value == min_k {
                last_min = i as i64;
            }
            if value == max_k {
                last_max = i as i64;
            }
            let bound = if last_min < last_max {
                last_min
            } else {
                last_max
            };
            let add = if bound > last_bad { bound - last_bad } else { 0 };
            result = result + add;
            i = i + 1;
        }

        result
    }
}

}
