use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn can_reach(n: int, m: int) -> bool
        decreases if n > 0 { n } else { 0 },
    {
        if n == m {
            true
        } else if n < m || n % 3 != 0 || n < 3 {
            false
        } else {
            Self::can_reach(n / 3, m) || Self::can_reach(n - n / 3, m)
        }
    }

    pub fn can_obtain(n: i64, m: i64) -> (res: bool)
        requires
            1 <= n <= 1000000000,
            1 <= m <= 1000000000,
        ensures
            res == Self::can_reach(n as int, m as int),
    {
    }
}

}