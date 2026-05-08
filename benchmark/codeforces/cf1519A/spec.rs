use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min_rb(r: int, b: int) -> int {
        if r <= b {
            r
        } else {
            b
        }
    }

    pub open spec fn spec_max_rb(r: int, b: int) -> int {
        if r <= b {
            b
        } else {
            r
        }
    }

    pub open spec fn spec_min_ceil_extra_per_small(r: int, b: int) -> int {
        let mn = Self::spec_min_rb(r, b);
        let mx = Self::spec_max_rb(r, b);
        if mx == mn {
            0
        } else {
            (mx - 1) / mn
        }
    }

    pub open spec fn spec_feasible_closed(r: int, b: int, d: int) -> bool {
        Self::spec_min_ceil_extra_per_small(r, b) <= d
    }

    pub fn beans_distributable(r: i64, b: i64, d: i64) -> (res: bool)
        requires
            1 <= r <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            0 <= d <= 1_000_000_000,
        ensures
            res == Self::spec_feasible_closed(r as int, b as int, d as int),
    {
    }
}

}
