use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing(s: Seq<i32>) -> bool {
        forall|i: int| 0 <= i < s.len() as int - 1 ==> #[trigger] s[i] <= s[i + 1]
    }

    pub open spec fn can_fix_with_one_change(nums: Seq<i32>) -> bool {
        Self::is_non_decreasing(nums)
        || exists|k: int, v: i32|
            0 <= k < nums.len() as int
            && Self::is_non_decreasing(#[trigger] nums.update(k, v))
    }

    pub fn check_possibility(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 10_000,
            forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            result <==> Self::can_fix_with_one_change(nums@),
    {
        
    }
}

} 
