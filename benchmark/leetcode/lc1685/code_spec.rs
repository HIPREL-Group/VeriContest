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
        let n = nums.len() as i32;
        let mut total_sum: i32 = 0;
        let mut i: i32 = 0;

        while i < n {
            total_sum = total_sum + nums[i as usize];
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut prefix: i32 = 0;
        i = 0;

        while i < n {
            let left = i * nums[i as usize] - prefix;
            let suffix = total_sum - prefix - nums[i as usize];
            let right = suffix - (n - 1 - i) * nums[i as usize];
            result.push(left + right);
            prefix = prefix + nums[i as usize];
            i = i + 1;
        }

        result
    }
}

}
