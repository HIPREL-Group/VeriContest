use vstd::prelude::*;
use vstd::math::{max as spec_max, min as spec_min, abs as spec_abs};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn abs(x: i32) -> (res: i32)
        requires 
            x > i32::MIN, 
        ensures 
            (res as int) == spec_abs(x as int), 
    {
        if x < 0 { -x } else { x }
    }

    pub fn max(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        if x >= y { x } else { y }
    }

    pub fn min(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_min(x as int, y as int)
    {
        if x <= y { x } else { y }
    }

    pub fn maximum_strong_pair_xor(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 50, 
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100, 
        ensures 
            forall |i: int, j: int| 
                0 <= i < nums.len() && 0 <= j < nums.len() &&
                spec_abs((nums[i] - nums[j]) as int) <= spec_min(nums[i] as int, nums[j] as int)
                ==> (nums[i] ^ nums[j]) <= res,
            exists |i: int, j: int| 
                0 <= i < nums.len() && 0 <= j < nums.len() &&
                spec_abs((nums[i] - nums[j]) as int) <= spec_min(nums[i] as int, nums[j] as int) &&
                (nums[i] ^ nums[j]) == res,
    {
        let mut max_xor = 0;
        
        for i in 0..nums.len() 
        {
            for j in i..nums.len() 
            {
                if Self::abs(nums[i] - nums[j]) <= Self::min(nums[i], nums[j]) {
                    let current_xor = nums[i] ^ nums[j];
                    max_xor = Self::max(max_xor, current_xor);
                }
            }
        }
        
        max_xor
    }
}

}