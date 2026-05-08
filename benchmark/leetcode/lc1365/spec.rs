use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_less_than(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() < val { 1int } else { 0int }) + Self::count_less_than(s.drop_last(), val)
        }
    }

    pub fn smaller_numbers_than_current(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] as int == Self::count_less_than(nums@, nums[i]),
    {
    }
}

}
