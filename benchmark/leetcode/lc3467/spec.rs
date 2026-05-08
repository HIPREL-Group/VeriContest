use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_even_count(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if nums[k - 1] as int % 2 == 0 {
        spec_even_count(nums, k - 1) + 1
    } else {
        spec_even_count(nums, k - 1)
    }
}

impl Solution {
    pub fn transform_array(nums: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            answer.len() == nums.len(),
            forall |i: int| 0 <= i < spec_even_count(nums@, nums.len() as int) ==> #[trigger] answer[i] == 0,
            forall |i: int| spec_even_count(nums@, nums.len() as int) <= i < nums.len() ==> #[trigger] answer[i] == 1,
    {
    }
}

} 
