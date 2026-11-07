use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;



pub open spec fn split_cost(nums: Seq<i32>, i: int, j: int) -> int {
    nums[0] as int + nums[i] as int + nums[j] as int
}


pub open spec fn spec_minimum_cost(nums: Seq<i32>) -> int {
    
    
    
    
    nums[0] as int + spec_two_smallest_sum(nums, nums.len() as int)
}



pub open spec fn spec_min1(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 1 {
        51  
    } else if (nums[k - 1] as int) < spec_min1(nums, k - 1) {
        nums[k - 1] as int
    } else {
        spec_min1(nums, k - 1)
    }
}

pub open spec fn spec_min2(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 1 {
        51
    } else if (nums[k - 1] as int) < spec_min1(nums, k - 1) {
        
        spec_min1(nums, k - 1)
    } else if (nums[k - 1] as int) < spec_min2(nums, k - 1) {
        nums[k - 1] as int
    } else {
        spec_min2(nums, k - 1)
    }
}

pub open spec fn spec_two_smallest_sum(nums: Seq<i32>, k: int) -> int {
    spec_min1(nums, k) + spec_min2(nums, k)
}

impl Solution {
    pub fn minimum_cost(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            
            result as int == spec_minimum_cost(nums@),
            
            exists |i: int, j: int|
                1 <= i < j < nums.len()
                && result as int == split_cost(nums@, i, j),
            
            forall |i: int, j: int|
                1 <= i < j < nums.len()
                ==> result as int <= split_cost(nums@, i, j),
    {
        let n = nums.len();
        let mut min1: i32 = 51;
        let mut min2: i32 = 51;
        let mut i: usize = 1;
        while i < n {
            if nums[i] < min1 {
                min2 = min1;
                min1 = nums[i];
            } else if nums[i] < min2 {
                min2 = nums[i];
            }
            i = i + 1;
        }
        nums[0] + min1 + min2
    }
}

} 
