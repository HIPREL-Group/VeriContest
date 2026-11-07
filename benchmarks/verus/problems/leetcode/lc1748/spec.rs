use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn occurrence_count(nums: Seq<i32>, val: int, j: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        occurrence_count(nums, val, j - 1)
            + if nums[j - 1] as int == val { 1int } else { 0int }
    }
}

pub open spec fn is_unique(nums: Seq<i32>, i: int) -> bool {
    occurrence_count(nums, nums[i] as int, nums.len() as int) == 1
}

pub open spec fn unique_sum(nums: Seq<i32>, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() {
        0
    } else {
        (if is_unique(nums, i) { nums[i] as int } else { 0int })
            + unique_sum(nums, i + 1)
    }
}

impl Solution {
    pub fn sum_of_unique(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            res as int == unique_sum(nums@, 0),
    {
    }
}

} 
