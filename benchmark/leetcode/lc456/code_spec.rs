use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_min_prefix(nums: Seq<i32>, j: int) -> i32
    recommends 0 <= j < nums.len()
    decreases j
{
    if j <= 0 {
        nums[0]
    } else if nums[j] < spec_min_prefix(nums, j - 1) {
        nums[j]
    } else {
        spec_min_prefix(nums, j - 1)
    }
}




pub struct Solution;

impl Solution {
    pub fn find132pattern(nums: Vec<i32>) -> (res: bool) 
        requires 
            1 <= nums.len() <= 20_000, 
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000, 
        ensures
            res == (exists |i: int, j: int, k: int| 
                0 <= i < j < k < nums.len() &&
                #[trigger] nums[i] < #[trigger] nums[k] < #[trigger] nums[j]), 
    {
        if nums.len() < 3 {
            
            return false;
        }

        let mut min_left: Vec<i32> = Vec::new();
        min_left.push(nums[0]);
        
        let mut m: usize = 1;
        while m < nums.len()
            decreases nums.len() - m
        {
            let prev = min_left[m - 1];
            let curr = nums[m];
            if curr < prev {
                min_left.push(curr);
            } else {
                min_left.push(prev);
            }
            m += 1;
        }

        let mut stack: Vec<i32> = Vec::new();

        let mut j: usize = nums.len() - 1;

        while j > 0
            decreases j
        {
            let current = nums[j];
            let l_min = min_left[j - 1];

            while stack.len() > 0 && *stack.last().unwrap() <= l_min
                decreases stack.len()
            {
                stack.pop();
                
            }

            if current > l_min {
                if stack.len() > 0 && *stack.last().unwrap() < current {
                    return true;
                }
                stack.push(current);
            }
            j -= 1;
        }
        
        false
    }
}
}
