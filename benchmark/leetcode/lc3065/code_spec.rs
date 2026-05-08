use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32) 
        requires 
            1 <= nums.len() <= 50, 
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000, 
            1 <= k <= 1_000_000_000, 
            exists |i: int| 0 <= i < nums.len() && nums[i] >= k, 
        ensures 
            (res as int) == nums@.filter(|x: i32| x < k).len(),
            0 <= res <= nums.len(), 
    {
        let mut count: i32 = 0;
        for i in 0..nums.len() 
        {
            if nums[i] < k {
                count += 1;
            }
        }
        
        return count;
    }
}

}