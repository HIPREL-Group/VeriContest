use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn has_even_digits(x: int) -> bool {
    (10 <= x && x <= 99) || (1000 <= x && x <= 9999) || x == 100000
}

pub open spec fn count_even(s: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_even(s, end - 1) + if has_even_digits(s[end - 1] as int) { 1int } else { 0int }
    }
}

impl Solution {
    pub fn find_numbers(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        ensures
            result as int == count_even(nums@, nums.len() as int),
    {
    }
}

}
