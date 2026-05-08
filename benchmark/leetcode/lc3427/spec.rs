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
    }
}

}
