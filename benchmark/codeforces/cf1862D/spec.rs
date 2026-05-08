use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tri(x: int) -> int {
        x * (x - 1) / 2
    }

    pub open spec fn witness_ok(n: int, res: int, m: int) -> bool {
        1 <= m <= 2_000_000_000
            && Self::tri(m) <= n
            && n < ((m + 1) * m / 2)
            && res == m + (n - Self::tri(m))
    }

    pub fn min_balls_for_types(n: u64) -> (res: u64)
        requires
            1 <= n <= 1_000_000_000_000_000_000u64,
        ensures
            exists|m: int| Self::witness_ok(n as int, res as int, m),
    {
    }
}

}
