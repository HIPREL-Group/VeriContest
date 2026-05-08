use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_sum(nums, k - 1) + nums[k - 1] as int
    }
}

impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            1 <= k <= 100,
        ensures
            result == spec_sum(nums@, nums.len() as int) % (k as int),
    {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            total += nums[i];
            i += 1;
        }
        ((total as u32) % (k as u32)) as i32
    }
}

} 
