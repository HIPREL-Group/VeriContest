use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_concatenation(nums: Vec<i32>) -> (ans: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            ans.len() == 2 * nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] ans[i] == nums[i],
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] ans[nums.len() as int + i] == nums[i],
    {
        let n = nums.len();
        let mut ans: Vec<i32> = vec![0i32; 2 * n];
        let mut i: usize = 0;

        while i < n
        {
            ans.set(i, nums[i]);
            ans.set(n + i, nums[i]);
            i += 1;
        }

        ans
    }
}

} 
