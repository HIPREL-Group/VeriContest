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

    proof fn lemma_min_max_from_exec(r: i64, b: i64, mn: i64, mx: i64)
        requires
            1 <= r <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            mn == if r <= b { r } else { b },
            mx == if r <= b { b } else { r },
        ensures
            mn as int == Self::spec_min_rb(r as int, b as int),
            mx as int == Self::spec_max_rb(r as int, b as int),
    {
    }

    proof fn lemma_spec_ceil_when_equal(r: i64, b: i64, mn: i64, mx: i64)
        requires
            1 <= r <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            mn == if r <= b { r } else { b },
            mx == if r <= b { b } else { r },
            mx == mn,
        ensures
            Self::spec_min_ceil_extra_per_small(r as int, b as int) == 0,
    {
        Self::lemma_min_max_from_exec(r, b, mn, mx);
        let ri = r as int;
        let bi = b as int;
        assert(Self::spec_min_rb(ri, bi) == Self::spec_max_rb(ri, bi));
    }

    proof fn lemma_spec_ceil_when_unequal(r: i64, b: i64, mn: i64, mx: i64, q: i64)
        requires
            1 <= r <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            mn == if r <= b { r } else { b },
            mx == if r <= b { b } else { r },
            mx != mn,
            q as int == (mx as int - 1) / (mn as int),
        ensures
            q as int == Self::spec_min_ceil_extra_per_small(r as int, b as int),
    {
        Self::lemma_min_max_from_exec(r, b, mn, mx);
        let ri = r as int;
        let bi = b as int;
        let smn = Self::spec_min_rb(ri, bi);
        let smx = Self::spec_max_rb(ri, bi);
        assert(smn == mn as int);
        assert(smx == mx as int);
        assert(smx != smn);
        assert((q as int) == (smx - 1) / smn);
    }

    pub fn beans_distributable(r: i64, b: i64, d: i64) -> (res: bool)
        requires
            1 <= r <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            0 <= d <= 1_000_000_000,
        ensures
            res == Self::spec_feasible_closed(r as int, b as int, d as int),
    {
        let mn = if r <= b { r } else { b };
        let mx = if r <= b { b } else { r };
        if mx == mn {
            proof {
                Self::lemma_spec_ceil_when_equal(r, b, mn, mx);
            }
            true
        } else {
            let q = (mx - 1) / mn;
            proof {
                Self::lemma_spec_ceil_when_unequal(r, b, mn, mx, q);
            }
            q <= d
        }
    }
}

}
