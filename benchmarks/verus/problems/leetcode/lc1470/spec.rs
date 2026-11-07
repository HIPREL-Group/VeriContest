use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn shuffle(nums: Vec<i32>, n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 500,
            nums.len() == 2 * n,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < n ==> #[trigger] result[2 * i] == nums[i],
            forall |i: int| 0 <= i < n ==> #[trigger] result[2 * i + 1] == nums[n as int + i],
    {
    }
}

} 
