use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_prefix(nums: Seq<i32>, len: int) -> bool
        decreases len,
    {
        if len <= 0 {
            true
        } else if len == 1 {
            false
        } else {
            let two_equal = nums[len - 2] == nums[len - 1] && Self::valid_prefix(nums, len - 2);
            let three_equal = len >= 3
                && nums[len - 3] == nums[len - 2]
                && nums[len - 2] == nums[len - 1]
                && Self::valid_prefix(nums, len - 3);
            let three_inc = len >= 3
                && nums[len - 3] + 1 == nums[len - 2]
                && nums[len - 2] + 1 == nums[len - 1]
                && Self::valid_prefix(nums, len - 3);
            two_equal || three_equal || three_inc
        }
    }

    pub fn valid_partition(nums: Vec<i32>) -> (ans: bool)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
        ensures
            ans == Self::valid_prefix(nums@, nums.len() as int),
    {
        let n = nums.len() as i32;
        let mut dp: Vec<i32> = Vec::new();
        dp.push(1);
        let mut i: i32 = 1;
        while i <= n {
            let mut cur: i32 = 0;
            if i >= 2 {
                if nums[(i - 2) as usize] == nums[(i - 1) as usize] && dp[(i - 2) as usize] == 1 {
                    cur = 1;
                }
            }
            if i >= 3 {
                if nums[(i - 3) as usize] == nums[(i - 2) as usize] && nums[(i - 2) as usize] == nums[(i - 1) as usize] && dp[(i - 3) as usize] == 1 {
                    cur = 1;
                }
                if nums[(i - 3) as usize] + 1 == nums[(i - 2) as usize] && nums[(i - 2) as usize] + 1 == nums[(i - 1) as usize] && dp[(i - 3) as usize] == 1 {
                    cur = 1;
                }
            }
            dp.push(cur);
            i = i + 1;
        }
        dp[n as usize] == 1
    }
}

}
