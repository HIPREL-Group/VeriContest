use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    fn tri_safe(x: u64) -> (t: u64)
        requires
            1 <= x <= 2_000_000_001u64,
        ensures
            t as int == (x as int) * ((x as int) - 1) / 2,
    {
        if x % 2 == 0 {
            proof {
                assert((x / 2) * (x - 1) <= u64::MAX) by (nonlinear_arith)
                    requires
                        1 <= x <= 2_000_000_001u64,
                {
                }
                assert((x as int) == 2 * ((x / 2) as int)) by (nonlinear_arith)
                    requires
                        (x as int) % 2 == 0,
                {
                }
                assert(((x / 2) as int) * ((x as int) - 1)
                    == (x as int) * ((x as int) - 1) / 2) by (nonlinear_arith)
                    requires
                        (x as int) == 2 * ((x / 2) as int),
                {
                }
            }
            (x / 2) * (x - 1)
        } else {
            proof {
                assert(x * ((x - 1) / 2) <= u64::MAX) by (nonlinear_arith)
                    requires
                        1 <= x <= 2_000_000_001u64,
                {
                }
                assert((x as int) - 1 == 2 * (((x - 1) / 2) as int)) by (nonlinear_arith)
                    requires
                        (x as int) % 2 == 1,
                {
                }
                assert((x as int) * (((x - 1) / 2) as int)
                    == (x as int) * ((x as int) - 1) / 2) by (nonlinear_arith)
                    requires
                        (x as int) - 1 == 2 * (((x - 1) / 2) as int),
                {
                }
            }
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
        while lo + 1 < hi
            invariant
                1 <= n,
                n <= 1_000_000_000_000_000_000u64,
                1u64 <= lo < hi <= 2_000_000_001u64,
                ((lo as int) * ((lo as int) - 1) / 2) <= (n as int),
                (n as int) < ((hi as int) * ((hi as int) - 1) / 2),
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            proof {
                assert(lo < mid < hi);
                assert(1 <= mid <= 2_000_000_001);
            }
            let tri_mid = Self::tri_safe(mid);
            if tri_mid <= n {
                lo = mid;
            } else {
                hi = mid;
            }
        }

        proof {
            assert(lo + 1 >= hi);
            assert(lo < hi);
            assert(hi == lo + 1);
        }

        let m = lo;
        let base = Self::tri_safe(m);
        let extra = n - base;
        let res = m + extra;
        proof {
            let mi = m as int;
            assert(1 <= mi <= 2_000_000_000) by (nonlinear_arith)
                requires
                    1 <= m <= 2_000_000_000u64,
                    mi == m as int,
            {
            }
                    assert(base as int == (m as int) * ((m as int) - 1) / 2);
            assert(Self::tri(mi) == (mi * (mi - 1)) / 2);
                    assert(Self::tri(mi + 1) == ((mi + 1) * mi) / 2);
            assert(Self::tri(mi) <= (n as int));
                    assert(hi == m + 1);
                    assert((n as int) < ((hi as int) * ((hi as int) - 1) / 2));
                    assert((n as int) < ((mi + 1) * mi / 2));
            assert(base as int == Self::tri(mi));
            assert(extra as int == n as int - Self::tri(mi));
            assert(res as int == mi + (n as int - Self::tri(mi)));
            assert(exists|mw: int| Self::witness_ok(n as int, res as int, mw)) by {
                let mw = mi;
                assert(1 <= mw <= 2_000_000_000);
                assert(Self::tri(mw) <= (n as int));
                assert((n as int) < ((mw + 1) * mw / 2));
                assert(res as int == mw + (n as int - Self::tri(mw)));
                assert(Self::witness_ok(n as int, res as int, mw));
            }
        }
        res
    }
}

}
