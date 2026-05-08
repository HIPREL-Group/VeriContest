use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum_of_squares(nums: Seq<i32>, n: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if n % k == 0 {
        spec_sum_of_squares(nums, n, k - 1) + (nums[k - 1] as int) * (nums[k - 1] as int)
    } else {
        spec_sum_of_squares(nums, n, k - 1)
    }
}

impl Solution {
    pub fn sum_of_squares(nums: Vec<i32>) -> (total: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            total == spec_sum_of_squares(nums@, nums.len() as int, nums.len() as int),
    {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if n % (i + 1) == 0 {
                total += nums[i] * nums[i];
            }
            i += 1;
        }
        total
    }
}

} 
