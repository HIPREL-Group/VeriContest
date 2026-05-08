use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn shuffle(nums: Vec<i32>, n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 500,
            nums.len() == 2 * n,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < n ==> #[trigger] result[2 * i] == nums[i],
            forall |i: int| 0 <= i < n ==> #[trigger] result[2 * i + 1] == nums[n as int + i],
    {
        let half = n as usize;
        let mut result: Vec<i32> = vec![0i32; 2 * half];
        let mut i: usize = 0;
        while i < half
            invariant
                1 <= n <= 500,
                half == n as usize,
                nums.len() == 2 * half,
                result.len() == 2 * half,
                0 <= i <= half,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
                forall |j: int| 0 <= j < i ==> #[trigger] result[2 * j] == nums[j],
                forall |j: int| 0 <= j < i ==> #[trigger] result[2 * j + 1] == nums[half as int + j],
            decreases half - i,
        {
            result.set(2 * i, nums[i]);
            result.set(2 * i + 1, nums[half + i]);
            i += 1;
        }
        result
    }
}

} 
