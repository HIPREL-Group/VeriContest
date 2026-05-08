use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_non_min_or_max(nums: Vec<i32>) -> (res: i32) 
        requires 
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures 
            nums.len() < 3 ==> res == -1,
            nums.len() >= 3 ==> {
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] == res
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] < res
                &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] > res
            },
    {
        if nums.len() < 3 {
            return -1;
        }

        let mut min_val = nums[0];
        let mut max_val = nums[0];

        let mut i = 1;
        while i < nums.len()
        {
            if nums[i] < min_val {
                min_val = nums[i];
            }
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        
        let mut j = 0;
        while j < nums.len()
        {
            if nums[j] != min_val && nums[j] != max_val {
                return nums[j];
            }
            j += 1;
        }

        -1
    }
}

}