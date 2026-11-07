use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn spec_max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn array_value_upto(s: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else { array_value_upto(s, n - 1) + abs_diff(s[n - 1] as int, s[n] as int) }
}

pub open spec fn array_value(s: Seq<i32>) -> int {
    array_value_upto(s, s.len() as int - 1)
}

pub open spec fn reversal_gain(s: Seq<i32>, l: int, r: int) -> int {
    let n = s.len() as int;
    let left_change = if l > 0 {
        abs_diff(s[l - 1] as int, s[r] as int) - abs_diff(s[l - 1] as int, s[l] as int)
    } else { 0int };
    let right_change = if r < n - 1 {
        abs_diff(s[l] as int, s[r + 1] as int) - abs_diff(s[r] as int, s[r + 1] as int)
    } else { 0int };
    left_change + right_change
}

impl Solution {
    pub fn max_value_after_reverse(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums@.len() <= 30000,
            forall |i: int| 0 <= i < nums@.len() ==> -100000 <= #[trigger] nums@[i] <= 100000,
            forall |l: int, r: int| 0 <= l && l <= r && r < nums@.len() ==>
                array_value(nums@) + #[trigger] reversal_gain(nums@, l, r) <= i32::MAX as int,
        ensures
            forall |l: int, r: int| 0 <= l && l <= r && r < nums@.len() ==>
                result as int >= array_value(nums@) + #[trigger] reversal_gain(nums@, l, r),
            exists |l: int, r: int| 0 <= l && l <= r && r < nums@.len() &&
                result as int == array_value(nums@) + reversal_gain(nums@, l, r),
    {
    }
}

}
