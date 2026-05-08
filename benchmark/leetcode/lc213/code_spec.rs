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
        let n = nums.len();
        if n == 1 {
            return nums[0];
        }
        let hi1: usize = n - 2;
        let rob1: i32;
        if hi1 == 0 {
            rob1 = nums[0];
        } else {
            let mut a: i32 = nums[0];
            let mut b: i32 = if nums[0] > nums[1] { nums[0] } else { nums[1] };
            let mut i: usize = 2;
            while i <= hi1 {
                let c = if a + nums[i] > b { a + nums[i] } else { b };
                a = b;
                b = c;
                i = i + 1;
            }
            rob1 = b;
        }
        let hi2: usize = n - 1;
        let rob2: i32;
        if n == 2 {
            rob2 = nums[1];
        } else {
            let mut a: i32 = nums[1];
            let mut b: i32 = if nums[1] > nums[2] { nums[1] } else { nums[2] };
            let mut i: usize = 3;
            while i <= hi2 {
                let c = if a + nums[i] > b { a + nums[i] } else { b };
                a = b;
                b = c;
                i = i + 1;
            }
            rob2 = b;
        }
        if rob1 > rob2 { rob1 } else { rob2 }
    }
}

} 
