use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

pub open spec fn spec_adj_diff(nums: Seq<i32>, n: int, j: int) -> int {
    if j == 0 {
        spec_abs(nums[0] as int - nums[n - 1] as int)
    } else {
        spec_abs(nums[j] as int - nums[j - 1] as int)
    }
}

pub open spec fn spec_max_diff(nums: Seq<i32>, n: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if spec_adj_diff(nums, n, k - 1) > spec_max_diff(nums, n, k - 1) {
        spec_adj_diff(nums, n, k - 1)
    } else {
        spec_max_diff(nums, n, k - 1)
    }
}

impl Solution {
    pub fn max_adjacent_distance(nums: Vec<i32>) -> (diff: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            diff == spec_max_diff(nums@, nums.len() as int, nums.len() as int),
    {
    }
}

} 
