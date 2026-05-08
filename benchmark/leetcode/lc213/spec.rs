use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rob_spec(nums: Seq<i32>, lo: int, hi: int) -> int
        recommends
            0 <= lo <= hi < nums.len(),
        decreases hi - lo,
    {
        if hi < lo {
            0
        } else if hi == lo {
            nums[lo] as int
        } else if hi == lo + 1 {
            if nums[lo] as int > nums[hi] as int { nums[lo] as int } else { nums[hi] as int }
        } else {
            let skip = Self::rob_spec(nums, lo, hi - 1);
            let take = Self::rob_spec(nums, lo, hi - 2) + nums[hi] as int;
            if take > skip { take } else { skip }
        }
    }

    pub fn rob(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result == if nums@.len() == 1 {
                nums@[0] as int
            } else {
                let n = nums@.len() as int;
                let r1 = Self::rob_spec(nums@, 0, n - 2);
                let r2 = Self::rob_spec(nums@, 1, n - 1);
                if r1 > r2 { r1 } else { r2 }
            },
    {
    }
}

} 
