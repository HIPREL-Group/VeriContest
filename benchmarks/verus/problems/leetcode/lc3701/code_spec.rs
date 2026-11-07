use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alternating_prefix(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::alternating_prefix(s, end - 1)
                + if (end - 1) % 2 == 0 {
                    s[end - 1] as int
                } else {
                    -(s[end - 1] as int)
                }
        }
    }

    pub fn alternating_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::alternating_prefix(nums@, nums.len() as int),
    {
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();
        while i < n {
            let old_i: usize = i;
            let prev: i32 = ans;
            if old_i % 2 == 0 {
                ans = prev + nums[old_i];
            } else {
                ans = prev - nums[old_i];
            }
            i = i + 1;
        }
        ans
    }
}

}
