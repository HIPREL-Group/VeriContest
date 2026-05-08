use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn ceil_div(n: int, a: int) -> int {
    (n + a - 1) / a
}

impl Solution {
    pub fn min_flagstones(n: u64, m: u64, a: u64) -> (result: u64)
        requires
            1 <= n <= 1_000_000_000,
            1 <= m <= 1_000_000_000,
            1 <= a <= 1_000_000_000,
        ensures
            result as int == ceil_div(n as int, a as int) * ceil_div(m as int, a as int),
    {
    }
}

}
