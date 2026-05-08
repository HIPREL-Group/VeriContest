use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_first_divisor_from(n: int, d: int) -> int
        recommends
            n >= 1,
            d >= 2,
        decreases if d <= n { n - d + 1 } else { 0 },
    {
        if d > n || d * d > n {
            n
        } else if n % d == 0 {
            d
        } else {
            Self::spec_first_divisor_from(n, d + 1)
        }
    }

    pub open spec fn spec_freedom_possible(n: int, m: int) -> bool {
        if n == 1 {
            true
        } else if m >= n {
            false
        } else {
            Self::spec_first_divisor_from(n, 2) > m
        }
    }

    pub fn freedom_possible(n: i64, m: i64) -> (res: bool)
        requires
            1 <= n as int <= 1_000_000_000,
            1 <= m as int <= 1_000_000_000,
        ensures
            res == Self::spec_freedom_possible(n as int, m as int),
    {
        if n == 1 {
            return true;
        }
        if m >= n {
            return false;
        }
        let mut d: i64 = 2;
        while d * d <= n {
            if n % d == 0 {
                return d > m;
            }
            d = d + 1;
        }
        true
    }
}

}
