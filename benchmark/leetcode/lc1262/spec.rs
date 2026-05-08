use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subset_sum(nums: Seq<i32>, sel: Seq<bool>, hi: int) -> int
    decreases hi
{
    if hi <= 0 { 0 }
    else {
        (if sel[hi - 1] { nums[hi - 1] as int } else { 0 })
        + subset_sum(nums, sel, hi - 1)
    }
}

impl Solution {
    pub fn max_sum_div_three(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 40000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
        ensures
            result >= 0,
            result as int % 3 == 0,
            exists |sel: Seq<bool>| sel.len() == nums.len() as int
                && subset_sum(nums@, sel, nums.len() as int) == result as int,
            forall |sel: Seq<bool>| sel.len() == nums.len() as int
                && subset_sum(nums@, sel, nums.len() as int) % 3 == 0
                ==> subset_sum(nums@, sel, nums.len() as int) <= result as int,
    {
    }
}

}
