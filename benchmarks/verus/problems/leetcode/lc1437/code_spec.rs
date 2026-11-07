use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn k_length_apart(nums: Vec<i32>, k: i32) -> (result: bool)
        requires
            1 <= nums.len() <= 100000,
            0 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1,
        ensures
            result == (forall |i: int, j: int| 0 <= i < j < nums.len() && #[trigger] nums[i] == 1 && #[trigger] nums[j] == 1 ==> j - i > k),
    {
        let n = nums.len();
        let k_usize = k as usize;
        let mut i: usize = 0;
        let mut seen_one = false;
        let mut prev_one: usize = 0;

        while i < n {
            if nums[i] == 1 {
                if seen_one {
                    if i - prev_one <= k_usize {
                        return false;
                    }
                }
                prev_one = i;
                seen_one = true;
            }
            i = i + 1;
        }

        true
    }
}

}
