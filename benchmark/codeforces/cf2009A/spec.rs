use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_value(a: int, b: int) -> int {
        b - a
    }

    pub fn minimize_value(a: i32, b: i32) -> (result: i32)
        requires
            1 <= a <= b <= 10,
        ensures
            result as int == Self::min_value(a as int, b as int),
            0 <= result <= 9,
    {
    }
}

}
