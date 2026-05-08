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

    pub open spec fn spec_ceil_sqrt(k: int) -> int {
        let f = Self::spec_floor_sqrt(k);
        if f * f == k {
            f
        } else {
            f + 1
        }
    }

    pub open spec fn spec_infinity_table_row(k: int) -> int {
        let s = Self::spec_ceil_sqrt(k);
        let off = k - (s - 1) * (s - 1);
        if off <= s {
            off
        } else {
            s
        }
    }

    pub open spec fn spec_infinity_table_col(k: int) -> int {
        let s = Self::spec_ceil_sqrt(k);
        let off = k - (s - 1) * (s - 1);
        if off <= s {
            s
        } else {
            2 * s - off
        }
    }

    pub fn infinity_table_cell(k: i64) -> (res: (i64, i64))
        requires
            1 <= k <= 1_000_000_000,
        ensures
            res.0 as int == Self::spec_infinity_table_row(k as int),
            res.1 as int == Self::spec_infinity_table_col(k as int),
    {
    }
}

}
