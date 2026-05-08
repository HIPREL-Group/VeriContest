use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_int(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

impl Solution {
    pub fn max_monkeys(m: u64, a: u64, b: u64, c: u64) -> (result: u64)
        requires
            1 <= m <= 100000000,
            1 <= a <= 100000000,
            1 <= b <= 100000000,
            1 <= c <= 100000000,
        ensures
            result as int == min_int(m as int, a as int) + min_int(m as int, b as int)
                + min_int(c as int, 2 * (m as int) - min_int(m as int, a as int) - min_int(m as int, b as int)),
    {
    }
}

}
