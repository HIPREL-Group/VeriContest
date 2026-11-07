use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_floor_sqrt_rec(lo: int, hi: int, n: int) -> int
        recommends
            0 <= lo < hi,
            lo * lo <= n,
            n < hi * hi,
        decreases hi - lo,
    {
        if lo + 1 >= hi {
            lo
        } else {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= n {
                Self::spec_floor_sqrt_rec(mid, hi, n)
            } else {
                Self::spec_floor_sqrt_rec(lo, mid, n)
            }
        }
    }

    pub open spec fn spec_floor_sqrt(n: int) -> int {
        if n <= 0 {
            0int
        } else {
            Self::spec_floor_sqrt_rec(0, n + 1, n)
        }
    }

    pub open spec fn spec_bulbs_on(n: int) -> int {
        n - Self::spec_floor_sqrt(n)
    }

    pub fn min_bulbs_n(k: u64) -> (n: u64)
        requires
            1 <= k <= 1_000_000_000_000_000_000u64,
        ensures
            Self::spec_bulbs_on(n as int) == k as int,
            forall|m: int|
                1 <= m < (n as int) ==> #[trigger] Self::spec_bulbs_on(m) < k as int,
    {
    }
}

}
