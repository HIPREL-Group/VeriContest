use vstd::prelude::*;
use std::collections::HashMap;

fn main() {}

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct Solution;

impl Solution {
    pub fn contains_nearby_duplicate(nums: Vec<i32>, k: i32) -> (res: bool) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 1 <= i < nums.len() ==> 
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= k <= 10_000,
        ensures 
            res == (exists |i: int, j: int| 0 <= i < j < nums.len() && 
                nums[i] == nums[j] && (j - i <= k as int)),
    {
        let mut map: HashMap<i32, usize> = HashMap::new();
        for i in 0..nums.len() 
        {
            if let Some(prev) = map.get(&nums[i]) {
                if i - *prev <= k as usize {
                    return true;
                }
            }
            map.insert(nums[i], i);
        }
        false
    }
}

}
