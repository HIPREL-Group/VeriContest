use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn ceil_div(n: int, d: int) -> int {
    (n + d - 1) / d
}

impl Solution {
    pub fn min_steps(x: u64) -> (result: u64)
        requires
            1 <= x <= 1_000_000,
        ensures
            result as int == ceil_div(x as int, 5),
    {
        (x + 4) / 5
    }
}

}
