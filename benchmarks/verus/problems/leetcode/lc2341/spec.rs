use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_val(s: Seq<i32>, v: int, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else {
            Self::count_val(s, v, end - 1) + if s[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn sum_pairs(s: Seq<i32>, v: int) -> int
        decreases (v + 1),
    {
        if v < 0 { 0 }
        else {
            Self::sum_pairs(s, v - 1) + Self::count_val(s, v, s.len() as int) / 2
        }
    }

    pub open spec fn sum_leftover(s: Seq<i32>, v: int) -> int
        decreases (v + 1),
    {
        if v < 0 { 0 }
        else {
            Self::sum_leftover(s, v - 1) + Self::count_val(s, v, s.len() as int) % 2
        }
    }

    pub fn number_of_pairs(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == 2,
            result[0] as int == Self::sum_pairs(nums@, 100),
            result[1] as int == Self::sum_leftover(nums@, 100),
    {
    }
}

}
