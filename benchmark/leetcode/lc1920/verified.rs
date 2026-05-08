use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn build_array(nums: Vec<i32>) -> (ans: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
        ensures
            ans.len() == nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] ans[i] == nums[nums[i] as int],
    {
        let n = nums.len();
        let mut ans = vec![0i32; n];
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= n <= 1000,
                ans.len() == n,
                forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] < nums.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] ans[j] == nums[nums[j] as int],
            decreases n - i,
        {
            ans.set(i, nums[nums[i] as usize]);
            i += 1;
        }
        ans
    }
}

}
