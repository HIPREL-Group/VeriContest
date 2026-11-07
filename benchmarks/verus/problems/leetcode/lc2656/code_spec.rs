use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_max(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 1 {
        nums[0] as int
    } else if nums[i - 1] > spec_max(nums, i - 1) {
        nums[i - 1] as int
    } else {
        spec_max(nums, i - 1)
    }
}

pub open spec fn spec_max_sum(m: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_max_sum(m, k - 1) + m + (k - 1)
    }
}

impl Solution {
    pub fn maximize_sum(nums: Vec<i32>, k: i32) -> (score: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            score == spec_max_sum(spec_max(nums@, nums.len() as int), k as int),
    {
        let n = nums.len();
        let mut max_val: i32 = nums[0];
        let mut i: usize = 1;
        while i < n {
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        let mut score: i32 = 0;
        let mut j: i32 = 0;
        while j < k {
            score += max_val + j;
            j += 1;
        }
        score
    }
}

} 
