use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_lt(nums: Seq<i32>, x: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_lt(nums, x, end - 1) + if (nums[end - 1] as int) < x { 1int } else { 0int }
        }
    }

    pub open spec fn count_eq(nums: Seq<i32>, x: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_eq(nums, x, end - 1) + if nums[end - 1] as int == x { 1int } else { 0int }
        }
    }

    pub open spec fn good_choice(nums: Seq<i32>, x: int) -> bool {
        Self::count_lt(nums, x, nums.len() as int) == x && Self::count_eq(nums, x, nums.len() as int) == 0
    }

    pub open spec fn count_ways_upto(nums: Seq<i32>, x: int) -> int
        decreases x,
    {
        if x <= 0 {
            0
        } else {
            Self::count_ways_upto(nums, x - 1) + if Self::good_choice(nums, x - 1) { 1int } else { 0int }
        }
    }

    pub fn count_ways(nums: Vec<i32>) -> (ans: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
        ensures
            ans as int == Self::count_ways_upto(nums@, nums.len() as int + 1),
    {
    }
}

}
