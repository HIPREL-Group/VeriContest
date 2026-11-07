use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_prefix_sum(nums: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::spec_prefix_sum(nums, k - 1) + nums[k - 1] as int
        }
    }

    pub open spec fn spec_range_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
    {
        Self::spec_prefix_sum(nums, r) - Self::spec_prefix_sum(nums, l)
    }

    pub open spec fn spec_start(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i < nums.len(),
    {
        if nums[i] as int > i {
            0
        } else {
            i - nums[i] as int
        }
    }

    pub open spec fn spec_total(nums: Seq<i32>, k: int) -> int
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::spec_total(nums, k - 1)
                + Self::spec_range_sum(nums, Self::spec_start(nums, k - 1), k)
        }
    }

    pub fn subarray_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::spec_total(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut i: usize = 0;
        while i < n {
            let next = prefix[i] + nums[i];
            prefix.push(next);
            i += 1;
        }

        let mut total: i32 = 0;
        i = 0;
        while i < n {
            let step: usize = nums[i] as usize;
            let mut l: usize = 0;
            if step <= i {
                l = i - step;
            }
            let delta = prefix[i + 1] - prefix[l];
            total += delta;
            i += 1;
        }

        total
    }
}

}
