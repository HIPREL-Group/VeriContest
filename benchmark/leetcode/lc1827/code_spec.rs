use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adjusted_val(nums: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            nums[0] as int
        } else {
            let prev = Self::adjusted_val(nums, i - 1);
            if (nums[i] as int) <= prev {
                prev + 1
            } else {
                nums[i] as int
            }
        }
    }

    pub open spec fn total_ops(nums: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0int
        } else {
            Self::total_ops(nums, i - 1) + (Self::adjusted_val(nums, i) - nums[i] as int)
        }
    }

    pub fn min_operations(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 5000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            res >= 0,
            forall |i: int| 0 <= i < nums.len() - 1 ==>
                #[trigger] Self::adjusted_val(nums@, i) < Self::adjusted_val(nums@, i + 1),
            forall |i: int| 0 <= i < nums.len() ==>
                #[trigger] Self::adjusted_val(nums@, i) >= nums[i] as int,
            res as int == Self::total_ops(nums@, (nums.len() - 1) as int),
    {
        let n = nums.len();
        let mut ops: i64 = 0;
        let mut prev: i64 = nums[0] as i64;
        let mut i: usize = 1;

        while i < n
        {
            if nums[i] as i64 <= prev {
                ops = ops + (prev + 1 - nums[i] as i64);
                prev = prev + 1;
            } else {
                prev = nums[i] as i64;
            }
            i += 1;
        }

        ops as i32
    }
}

} 
