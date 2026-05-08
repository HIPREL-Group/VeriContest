use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_one_is_sum_of_others(a: int, b: int, c: int) -> bool {
    a == b + c || b == a + c || c == a + b
}

impl Solution {
    pub fn one_is_sum_of_others(a: i64, b: i64, c: i64) -> (res: bool)
        requires
            0 <= a <= 20,
            0 <= b <= 20,
            0 <= c <= 20,
        ensures
            res == spec_one_is_sum_of_others(a as int, b as int, c as int),
    {
    }
}

}
