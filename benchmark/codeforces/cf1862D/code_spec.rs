use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    fn tri_safe(x: u64) -> (t: u64) {
        if x % 2 == 0 {
            (x / 2) * (x - 1)
        } else {
            x * ((x - 1) / 2)
        }
    }

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
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo + 1 < hi {
            let mid = lo + (hi - lo) / 2;
            let tri_mid = Self::tri_safe(mid);
            if tri_mid <= n {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let m = lo;
        let base = Self::tri_safe(m);
        let extra = n - base;
        let res = m + extra;
        res
    }
}

}
