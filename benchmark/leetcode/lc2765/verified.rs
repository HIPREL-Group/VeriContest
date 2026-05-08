use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn dp_end(nums: Seq<i32>, k: int) -> int
        decreases if k <= 0 { 0int } else { k }
    {
        if k <= 0 {
            -1
        } else {
            let prev = Self::dp_end(nums, k - 1);
            if k >= 2 && prev > 0 && nums[k] == nums[k - 2] {
                prev + 1
            } else if nums[k] == nums[k - 1] + 1 {
                2
            } else {
                -1
            }
        }
    }

    pub open spec fn best_upto(nums: Seq<i32>, k: int) -> int
        decreases if k <= 0 { 0int } else { k }
    {
        if k <= 0 {
            -1
        } else {
            let prev = Self::best_upto(nums, k - 1);
            let cur = Self::dp_end(nums, k);
            if prev >= cur { prev } else { cur }
        }
    }

    pub fn alternating_subarray(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            result as int == Self::best_upto(nums@, nums.len() as int - 1),
    {
        let mut dp: i32 = -1;
        let mut res: i32 = -1;
        let mut i: usize = 1;
        while i < nums.len()
            invariant
                2 <= nums.len() <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
                1 <= i <= nums.len(),
                -1 <= dp <= i as i32,
                -1 <= res <= i as i32,
                dp as int == Self::dp_end(nums@, i as int - 1),
                res as int == Self::best_upto(nums@, i as int - 1),
            decreases nums.len() - i,
        {
            if dp > 0 && nums[i] == nums[i - 2] {
                dp = dp + 1;
            } else if nums[i] == nums[i - 1] + 1 {
                dp = 2;
            } else {
                dp = -1;
            }
            if dp > res {
                res = dp;
            }
            i = i + 1;
        }
        res
    }
}

}
