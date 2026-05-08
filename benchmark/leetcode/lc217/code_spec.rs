use vstd::prelude::*;
use std::collections::HashSet;

fn main() {}

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct Solution;

impl Solution {
    pub fn contains_duplicate(nums: Vec<i32>) -> (res: bool) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 1 <= i < nums.len() ==> 
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures 
            res == (exists |i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j]),
    {
        let mut seen = HashSet::new();
        for i in 0..nums.len() 
        {
            if seen.contains(&nums[i]) {
                return true;
            }
            seen.insert(nums[i]);
        }
        false
    }
}

}