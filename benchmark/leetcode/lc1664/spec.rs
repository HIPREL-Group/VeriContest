use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_even(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else if start % 2 == 0 {
        s[start] as int + sum_even(s, start + 1, end)
    } else {
        sum_even(s, start + 1, end)
    }
}

pub open spec fn sum_odd(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else if start % 2 == 1 {
        s[start] as int + sum_odd(s, start + 1, end)
    } else {
        sum_odd(s, start + 1, end)
    }
}

pub open spec fn even_sum_after_removal(s: Seq<i32>, i: int) -> int {
    sum_even(s, 0, i) + sum_odd(s, i + 1, s.len() as int)
}

pub open spec fn odd_sum_after_removal(s: Seq<i32>, i: int) -> int {
    sum_odd(s, 0, i) + sum_even(s, i + 1, s.len() as int)
}

pub open spec fn is_fair_after_removal(s: Seq<i32>, i: int) -> bool {
    even_sum_after_removal(s, i) == odd_sum_after_removal(s, i)
}

pub open spec fn count_fair(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else if is_fair_after_removal(s, start) {
        1 + count_fair(s, start + 1, end)
    } else {
        count_fair(s, start + 1, end)
    }
}

impl Solution {
    pub fn ways_to_make_fair(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            res == count_fair(nums@, 0, nums@.len() as int),
    {
    }
}

}
