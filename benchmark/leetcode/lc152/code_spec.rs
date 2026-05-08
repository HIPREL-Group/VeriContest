use vstd::prelude::*;
use vstd::math::{max as spec_max};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn product_of_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            1
        } else {
            nums[start] as int * Self::product_of_range(nums, start + 1, end)
        }
    }

    pub fn max(x: i32, y: i32) -> (res: i32)
        ensures (res as int) == spec_max(x as int, y as int)
    {
        if x >= y { x } else { y }
    }

    pub fn max_product(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 20_000, 
            forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10, 
            forall |i: int, j: int| 0 <= i < j <= nums.len()
                ==> i32::MIN <= #[trigger] Self::product_of_range(nums@, i, j) <= i32::MAX, 
        ensures 
            exists |i: int, j: int| 0 <= i < j <= nums.len() 
                && res == Self::product_of_range(nums@, i, j)
                && forall |k: int, l: int| 0 <= k < l <= nums.len() 
                    ==> res >= Self::product_of_range(nums@, k, l)
    {
        let n = nums.len();
        let mut ans: i32 = nums[0];
        
        for i in 0..n
        {
            let mut prod: i32 = 1;
            for j in i..n
            {
                prod = prod * nums[j];
                ans = Self::max(ans, prod);
            }
        }
        
        ans
    }
}

}