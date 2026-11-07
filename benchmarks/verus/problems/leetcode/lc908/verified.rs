use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_min(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if nums.len() == 0 {
            0
        } else if n <= 1 {
            nums[0] as int
        } else if n > nums.len() {
            Self::prefix_min(nums, nums.len() as int)
        } else {
            let prev = Self::prefix_min(nums, n - 1);
            let cur = nums[n - 1] as int;
            if prev < cur { prev } else { cur }
        }
    }

    pub open spec fn prefix_max(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if nums.len() == 0 {
            0
        } else if n <= 1 {
            nums[0] as int
        } else if n > nums.len() {
            Self::prefix_max(nums, nums.len() as int)
        } else {
            let prev = Self::prefix_max(nums, n - 1);
            let cur = nums[n - 1] as int;
            if prev > cur { prev } else { cur }
        }
    }

    pub open spec fn min_score(nums: Seq<i32>, k: int) -> int
    {
        if nums.len() == 0 {
            0
        } else {
            let diff = Self::prefix_max(nums, nums.len() as int) - Self::prefix_min(nums, nums.len() as int);
            if diff <= 2 * k { 0 } else { diff - 2 * k }
        }
    }

    pub fn smallest_range_i(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 10_000,
            0 <= k <= 10_000,
        ensures
            res as int == Self::min_score(nums@, k as int),
    {
        let n = nums.len();
        let mut i: usize = 1;
        let mut min_v = nums[0];
        let mut max_v = nums[0];

        while i < n
            invariant
                1 <= n <= 10_000,
                n == nums.len(),
                1 <= i <= n,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 10_000,
                min_v as int == Self::prefix_min(nums@, i as int),
                max_v as int == Self::prefix_max(nums@, i as int),
                0 <= min_v <= 10_000,
                0 <= max_v <= 10_000,
                min_v <= max_v,
            decreases n - i,
        {
            let v = nums[i];
            let old_min = min_v;
            let old_max = max_v;
            min_v = if old_min < v { old_min } else { v };
            max_v = if old_max > v { old_max } else { v };
            i += 1;
        }

        let diff = max_v - min_v;
        if diff <= 2 * k {
            0
        } else {
            diff - 2 * k
        }
    }
}

}
