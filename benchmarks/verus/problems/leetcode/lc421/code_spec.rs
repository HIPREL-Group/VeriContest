use vstd::prelude::*;
use std::collections::HashSet;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_maximum_xor(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 200_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX, 
        ensures 
            forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                ==> res >= (nums[i] ^ nums[j]),
            exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                && res == (nums[i] ^ nums[j]),
            res >= 0,
    {
        if nums.len() == 1 {
            return 0;
        }

        let mut max_xor = 0;
        let mut bit = 30;
        let mut mask: i32 = 0;

        while bit >= 0 
        {
            mask = mask | (1i32 << bit as u32);
            let mut prefixes: std::collections::HashSet<i32> = std::collections::HashSet::new(); 
            
            for i in 0..nums.len() 
            {
                let prefix = nums[i] & mask;
                prefixes.insert(prefix);
            }

            let target = max_xor | (1i32 << bit as u32);
            let mut found = false;
            
            for j in 0..nums.len()
            {
                let xor_val = (nums[j] & mask) ^ target;
                if !found && prefixes.contains(&xor_val) {
                    found = true;
                } else if !found {
                }
            }
            
            if found {
                max_xor = target;
            } else {
            }
            
            bit -= 1;
        }

        max_xor
    }
}

}