use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn sum_abs_diffs(nums: Seq<i32>, i: int, j: int) -> int
    decreases nums.len() - j,
{
    if j >= nums.len() {
        0
    } else {
        spec_abs(nums[i] as int - nums[j] as int) + sum_abs_diffs(nums, i, j + 1)
    }
}

impl Solution {
    pub fn get_sum_absolute_differences(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < nums@.len() ==> nums@[i] <= nums@[j],
        ensures
            result@.len() == nums@.len(),
            forall |i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] as int == sum_abs_diffs(nums@, i, 0),
    {
    }
}

}
