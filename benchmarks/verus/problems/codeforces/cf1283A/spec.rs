use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_minutes_before_new_year(h: int, m: int) -> int {
    1440 - 60 * h - m
}

impl Solution {
    pub fn minutes_before_new_year_one(h: i32, m: i32) -> (result: i32)
        requires
            0 <= h < 24,
            0 <= m < 60,
            !(h == 0 && m == 0),
        ensures
            result as int == spec_minutes_before_new_year(h as int, m as int),
    {
    }
}

}
