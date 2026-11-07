use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

pub open spec fn asc_sum_ending_at(nums: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        nums[0] as int
    } else if nums[i] > nums[i - 1] {
        asc_sum_ending_at(nums, i - 1) + nums[i] as int
    } else {
        nums[i] as int
    }
}

pub open spec fn max_val(nums: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo + 1
{
    if lo > hi {
        0
    } else if lo == hi {
        asc_sum_ending_at(nums, hi)
    } else {
        let a = asc_sum_ending_at(nums, hi);
        let b = max_val(nums, lo, hi - 1);
        if a >= b { a } else { b }
    }
}

impl Solution {
    pub fn max_ascending_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (max_val(nums@, 0, (nums.len() - 1) as int) as i32),
    {
    }
}
}
