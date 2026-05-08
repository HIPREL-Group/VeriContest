use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::prefix_sum(nums, k - 1) + nums[k - 1] as int
        }
    }

    pub fn min_start_value(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            result >= 1,
            exists|k: int| 0 <= k <= nums.len() && result == 1 - Self::prefix_sum(nums@, k),
            forall|k: int| 0 <= k <= nums.len() ==> 1 - Self::prefix_sum(nums@, k) <= result,
    {
        let n = nums.len();
        let mut min_sum: i32 = 0;
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + nums[i];
            if sum < min_sum {
                min_sum = sum;
            }
            i += 1;
        }
        1 - min_sum
    }
}

}
