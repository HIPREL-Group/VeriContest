use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn xor_sum_rec(nums: Seq<i32>, idx: int, current_xor: i32) -> int
    decreases nums.len() - idx,
{
    if idx >= nums.len() {
        current_xor as int
    } else {
        xor_sum_rec(nums, idx + 1, current_xor ^ nums[idx])
        + xor_sum_rec(nums, idx + 1, current_xor)
    }
}

impl Solution {
    pub fn subset_xor_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 12,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20,
        ensures
            result as int == xor_sum_rec(nums@, 0, 0i32),
    {
        Self::dfs(&nums, 0, 0)
    }

    fn dfs(nums: &Vec<i32>, idx: usize, current_xor: i32) -> (result: i32)
        requires
            idx <= nums.len() <= 12,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20,
            0 <= current_xor <= 31,
        ensures
            result as int == xor_sum_rec(nums@, idx as int, current_xor),
        decreases nums.len() - idx,
    {
        if idx == nums.len() {
            return current_xor;
        }
        let include = Self::dfs(nums, idx + 1, current_xor ^ nums[idx]);
        let exclude = Self::dfs(nums, idx + 1, current_xor);
        include + exclude
    }
}

}
