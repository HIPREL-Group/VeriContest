use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn build_number(s: int, d: int) -> int
    decreases d,
{
    if s <= 0 || d <= 0 {
        0int
    } else if d <= s {
        build_number(s - d, d - 1) * 10 + d
    } else {
        build_number(s, d - 1)
    }
}

impl Solution {
    pub fn min_varied(s: u32) -> (result: u32)
        requires
            1 <= s <= 45,
        ensures
            result as int == build_number(s as int, 9),
    {
    }
}

}
