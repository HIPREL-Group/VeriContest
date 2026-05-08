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
        decreases
            hi - lo,
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
}

pub open spec fn spec_answer(n: int) -> int
    recommends
        n >= 1,
{
    let m = 2 * n - 1;
    let k = Solution::spec_floor_sqrt(m);
    if k < 3 {
        0
    } else {
        (k + 1) / 2 - 1
    }
}

pub open spec fn is_valid_odd_a(n: int, a: int) -> bool {
    3 <= a && a % 2 == 1 && a * a + 1 <= 2 * n
}

impl Solution {
    pub fn floor_sqrt_u64(m: u64) -> (r: u64)
        requires
            1 <= m <= 2_000_000_000u64,
        ensures
            r as int == Self::spec_floor_sqrt(m as int),
            r <= 2_000_000_000u64,
    {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mid * mid <= m {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let r = lo - 1;
        r
    }

    pub fn vasya_pythagorean_triples_count(n: u64) -> (result: u64)
        requires
            1 <= n <= 1_000_000_000u64,
        ensures
            result as int == spec_answer(n as int),
            forall |a: int| #[trigger] is_valid_odd_a(n as int, a) ==> a <= Self::spec_floor_sqrt(2 * (n as int) - 1),
            forall |a: int|
                (3 <= a && a % 2 == 1 && a <= Self::spec_floor_sqrt(2 * (n as int) - 1)) ==> #[trigger] is_valid_odd_a(
                    n as int,
                    a,
                ),
    {
        let m = 2 * n - 1;
        let k = Self::floor_sqrt_u64(m);
        if k < 3 {
            0
        } else {
            let res = (k + 1) / 2 - 1;
            res
        }
    }
}

}
