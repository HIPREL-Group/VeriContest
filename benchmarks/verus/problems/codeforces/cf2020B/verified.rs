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

    pub fn floor_sqrt_u64(x: u64) -> (r: u64)
        requires
            1 <= x <= 1_000_000_002_000_001_000u64,
        ensures
            r as int == Self::spec_floor_sqrt(x as int),
            r <= 2_000_000_000u64,
    {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo < hi
            invariant
                1u64 <= x <= 1_000_000_002_000_001_000u64,
                1u64 <= lo <= hi <= 2_000_000_001u64,
                (lo - 1) * (lo - 1) <= x,
                x < hi * hi,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            proof {
                assert(lo <= mid) by (nonlinear_arith)
                    requires
                        lo < hi,
                        mid == lo + (hi - lo) / 2,
                {
                }
                assert(mid < hi) by (nonlinear_arith)
                    requires
                        lo < hi,
                        mid == lo + (hi - lo) / 2,
                {
                }
                assert(mid <= 2_000_000_000u64) by (nonlinear_arith)
                    requires
                        mid < hi,
                        hi <= 2_000_000_001u64,
                {
                }
            }
            proof {
                assert(mid * mid <= 4_000_000_004_000_000_001u64) by (nonlinear_arith)
                    requires
                        mid <= 2_000_000_000u64,
                {
                }
            }
            if mid * mid <= x {
                lo = mid + 1;
                proof {
                    assert((lo - 1) == mid);
                    assert((lo - 1) * (lo - 1) <= x);
                }
            } else {
                hi = mid;
                proof {
                    assert(x < hi * hi);
                }
            }
        }
        let r = lo - 1;
        proof {
            assert(lo == hi);
            assert(r <= 2_000_000_000u64) by (nonlinear_arith)
                requires
                    lo <= 2_000_000_001u64,
                    r == lo - 1,
            {
            }
            assert(r * r <= x);
            assert(x < (r + 1) * (r + 1));
            Self::lemma_exec_sqrt_matches_spec(x, r);
        }
        r
    }

    pub fn min_bulbs_n(k: u64) -> (n: u64)
        requires
            1 <= k <= 1_000_000_000_000_000_000u64,
        ensures
            Self::spec_bulbs_on(n as int) == k as int,
            forall|m: int|
                1 <= m < (n as int) ==> #[trigger] Self::spec_bulbs_on(m) < k as int,
    {
        proof {
            Self::lemma_ub_bulbs(k);
        }
        let ub = k + 2_000_000_000u64 + 1000u64;
        let mut lo = 1u64;
        let mut hi = ub;
        while lo < hi
            invariant
                1 <= k <= 1_000_000_000_000_000_000u64,
                ub == k + 2_000_000_000u64 + 1000u64,
                1u64 <= lo <= hi <= ub,
                Self::spec_bulbs_on(hi as int) >= k as int,
                lo == 1u64 || Self::spec_bulbs_on((lo - 1) as int) < k as int,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            proof {
                assert(lo <= mid) by (nonlinear_arith)
                    requires
                        lo < hi,
                        mid == lo + (hi - lo) / 2,
                {
                }
                assert(mid < hi) by (nonlinear_arith)
                    requires
                        lo < hi,
                        mid == lo + (hi - lo) / 2,
                {
                }
                assert(mid <= ub);
                assert(mid <= 1_000_000_002_000_001_000u64) by (nonlinear_arith)
                    requires
                        mid <= ub,
                        ub == k + 2_000_000_000 + 1000,
                        k <= 1_000_000_000_000_000_000,
                {
                }
            }
            let s = Self::floor_sqrt_u64(mid);
            proof {
                Self::lemma_spec_sqrt_bounds(mid as int);
                assert((s as int) * (s as int) <= mid as int);
                assert((s as int) <= mid as int) by (nonlinear_arith)
                    requires
                        (s as int) >= 0,
                        mid as int >= 1,
                        (s as int) * (s as int) <= mid as int,
                {
                }
            }
            let cnt = mid - s;
            if cnt >= k {
                hi = mid;
                proof {
                    assert(s as int == Self::spec_floor_sqrt(mid as int));
                    assert(Self::spec_bulbs_on(mid as int) == cnt as int);
                    assert(Self::spec_bulbs_on(hi as int) >= k as int);
                    assert(lo == 1u64 || Self::spec_bulbs_on((lo - 1) as int) < k as int);
                }
            } else {
                proof {
                    Self::lemma_spec_sqrt_bounds(mid as int);
                    assert(s as int == Self::spec_floor_sqrt(mid as int));
                    assert(Self::spec_bulbs_on(mid as int) == cnt as int);
                    assert(Self::spec_bulbs_on(mid as int) < k as int);
                    Self::lemma_m_le_mid_impl(mid as int, k as int);
                }
                lo = mid + 1;
                proof {
                    assert(Self::spec_bulbs_on((lo - 1) as int) < k as int);
                    assert(Self::spec_bulbs_on(hi as int) >= k as int);
                }
            }
        }
        proof {
            assert(lo == hi);
            assert(Self::spec_bulbs_on(lo as int) >= k as int);
            assert(lo == 1u64 || Self::spec_bulbs_on((lo - 1) as int) < k as int);
            Self::lemma_bulbs_at_one();
            assert(lo != 1u64) by {
                if lo == 1u64 {
                    assert(Self::spec_bulbs_on(1) >= k as int);
                    assert(0 >= k as int);
                }
            }
            Self::lemma_bulbs_step((lo - 1) as int);
            assert(Self::spec_bulbs_on(lo as int) <= Self::spec_bulbs_on((lo - 1) as int) + 1);
            assert(Self::spec_bulbs_on(lo as int) == k as int);
            assert forall|m: int| 1 <= m < (lo as int) implies Self::spec_bulbs_on(m) < k as int by {
                assert(1 <= m && m < lo as int);
                assert(m <= (lo - 1) as int) by (nonlinear_arith)
                    requires
                        m < lo as int,
                        lo as int >= 2,
                        m >= 1,
                {
                }
                Self::lemma_m_le_mid_impl((lo - 1) as int, k as int);
            }
        }
        lo
    }

    proof fn lemma_spec_floor_sqrt_rec_bounds(lo: int, hi: int, n: int)
        requires
            0 <= lo < hi,
            lo * lo <= n,
            n < hi * hi,
        ensures
            ({
                let r = Self::spec_floor_sqrt_rec(lo, hi, n);
                r >= 0 && r * r <= n && n < (r + 1) * (r + 1)
            }),
        decreases hi - lo,
    {
        if lo + 1 >= hi {
            assert(hi == lo + 1);
            let r = lo;
            assert(r >= 0);
            assert(r * r <= n);
            assert(n < (r + 1) * (r + 1));
        } else {
            let mid = lo + (hi - lo) / 2;
            assert(lo < mid && mid < hi);
            if mid * mid <= n {
                assert(0 <= mid < hi);
                assert(mid * mid <= n);
                assert(n < hi * hi);
                Self::lemma_spec_floor_sqrt_rec_bounds(mid, hi, n);
                let r = Self::spec_floor_sqrt_rec(mid, hi, n);
                assert(r >= 0 && r * r <= n && n < (r + 1) * (r + 1));
            } else {
                assert(mid * mid > n);
                assert(0 <= lo < mid);
                assert(lo * lo <= n);
                assert(n < mid * mid);
                Self::lemma_spec_floor_sqrt_rec_bounds(lo, mid, n);
                let r = Self::spec_floor_sqrt_rec(lo, mid, n);
                assert(r >= 0 && r * r <= n && n < (r + 1) * (r + 1));
            }
        }
    }

    proof fn lemma_spec_sqrt_bounds(n: int)
        requires
            n >= 1,
        ensures
            ({
                let r = Self::spec_floor_sqrt(n);
                r >= 0 && r * r <= n && n < (r + 1) * (r + 1)
            }),
    {
        assert(n < (n + 1) * (n + 1)) by (nonlinear_arith)
            requires
                n >= 1,
        {
        }
        assert(0 * 0 <= n);
        Self::lemma_spec_floor_sqrt_rec_bounds(0, n + 1, n);
        assert(Self::spec_floor_sqrt(n) == Self::spec_floor_sqrt_rec(0, n + 1, n));
    }

    proof fn lemma_bulbs_at_one()
        ensures
            Self::spec_bulbs_on(1) == 0,
    {
        Self::lemma_spec_sqrt_bounds(1);
        let r = Self::spec_floor_sqrt(1);
        assert(r * r <= 1);
        assert(1 < (r + 1) * (r + 1));
        assert(r != 0) by {
            if r == 0 {
                assert(1 < 1);
            }
        }
        assert(r < 2) by {
            if r >= 2 {
                assert(r * r >= 4) by (nonlinear_arith)
                    requires
                        r >= 2,
                {
                }
                assert(r * r <= 1);
                assert(false);
            }
        }
        assert(r == 1);
        assert(Self::spec_bulbs_on(1) == 0);
    }

    proof fn lemma_unique_sqrt(n: int, a: int, b: int)
        requires
            n >= 1,
            a >= 0,
            b >= 0,
            a * a <= n,
            n < (a + 1) * (a + 1),
            b * b <= n,
            n < (b + 1) * (b + 1),
        ensures
            a == b,
    {
        if a < b {
            assert(b >= a + 1);
            assert(b * b >= (a + 1) * (a + 1)) by (nonlinear_arith)
                requires
                    b >= a + 1,
                    a >= 0,
                    b >= 0,
            {
            }
            assert(n >= b * b);
            assert(n >= (a + 1) * (a + 1));
            assert(n < (a + 1) * (a + 1));
            assert(false);
        } else if a > b {
            assert(a >= b + 1);
            assert(a * a >= (b + 1) * (b + 1)) by (nonlinear_arith)
                requires
                    a >= b + 1,
                    a >= 0,
                    b >= 0,
            {
            }
            assert(n >= a * a);
            assert(n >= (b + 1) * (b + 1));
            assert(n < (b + 1) * (b + 1));
            assert(false);
        } else {
            assert(a == b);
        }
    }

    proof fn lemma_sqrt_upper_bound(x: int)
        requires
            1 <= x <= 1_000_000_002_000_001_000,
        ensures
            Self::spec_floor_sqrt(x) <= 2_000_000_000,
    {
        assert(2_000_000_001 * 2_000_000_001 == 4_000_000_004_000_000_001);
        assert(x < 2_000_000_001 * 2_000_000_001);
        let r = Self::spec_floor_sqrt(x);
        Self::lemma_spec_sqrt_bounds(x);
        assert(r * r <= x);
        assert(r >= 0);
        assert(r < 2_000_000_001) by (nonlinear_arith)
            requires
                r * r <= x,
                x < 2_000_000_001 * 2_000_000_001,
                r >= 0,
        {
        }
        assert(r <= 2_000_000_000);
    }

    proof fn lemma_ub_bulbs(k: u64)
        requires
            1 <= k <= 1_000_000_000_000_000_000u64,
        ensures
            Self::spec_bulbs_on((k + 2_000_000_000u64 + 1000u64) as int) >= k as int,
    {
        let ub = (k + 2_000_000_000u64 + 1000u64) as int;
        assert(ub <= 1_000_000_002_000_001_000);
        Self::lemma_sqrt_upper_bound(ub);
        assert(Self::spec_floor_sqrt(ub) <= 2_000_000_000);
        assert(ub - 2_000_000_000 >= k as int) by (nonlinear_arith)
            requires
                ub == k as int + 2_000_000_000 + 1000,
                k as int >= 1,
                k as int <= 1_000_000_000_000_000_000,
        {
        }
        assert(Self::spec_bulbs_on(ub) >= k as int);
    }

    proof fn lemma_bulbs_step(n: int)
        requires
            n >= 1,
        ensures
            Self::spec_bulbs_on(n + 1) >= Self::spec_bulbs_on(n),
            Self::spec_bulbs_on(n + 1) <= Self::spec_bulbs_on(n) + 1,
    {
        let sn = Self::spec_floor_sqrt(n);
        let sn1 = Self::spec_floor_sqrt(n + 1);
        Self::lemma_spec_sqrt_bounds(n);
        Self::lemma_spec_sqrt_bounds(n + 1);
        assert(sn >= 0);
        assert(sn1 >= 0);
        assert(sn * sn <= n);
        assert(n < (sn + 1) * (sn + 1));
        assert(sn1 * sn1 <= n + 1);
        assert(n + 1 < (sn1 + 1) * (sn1 + 1));
        assert(sn1 == sn || sn1 == sn + 1) by (nonlinear_arith)
            requires
                sn * sn <= n,
                n < (sn + 1) * (sn + 1),
                sn1 * sn1 <= n + 1,
                n + 1 < (sn1 + 1) * (sn1 + 1),
                sn >= 0,
                sn1 >= 0,
        {
        }
        if sn1 == sn + 1 {
            assert(Self::spec_bulbs_on(n + 1) == n + 1 - (sn + 1));
            assert(Self::spec_bulbs_on(n + 1) == Self::spec_bulbs_on(n));
        } else {
            assert(sn1 == sn);
            assert(Self::spec_bulbs_on(n + 1) == Self::spec_bulbs_on(n) + 1);
        }
    }

    proof fn lemma_bulbs_mono_range(a: int, b: int)
        requires
            1 <= a <= b,
        ensures
            Self::spec_bulbs_on(a) <= Self::spec_bulbs_on(b),
        decreases b - a,
    {
        if a < b {
            Self::lemma_bulbs_step(a);
            assert(Self::spec_bulbs_on(a) <= Self::spec_bulbs_on(a + 1));
            Self::lemma_bulbs_mono_range(a + 1, b);
            assert(Self::spec_bulbs_on(a + 1) <= Self::spec_bulbs_on(b));
        }
    }

    proof fn lemma_m_le_mid_impl(mid: int, k: int)
        requires
            mid >= 1,
            Self::spec_bulbs_on(mid) < k,
        ensures
            forall|m: int| 1 <= m <= mid ==> #[trigger] Self::spec_bulbs_on(m) < k,
    {
        assert forall|m: int| 1 <= m <= mid implies Self::spec_bulbs_on(m) < k by {
            assert(1 <= m && m <= mid);
            Self::lemma_bulbs_mono_range(m, mid);
            assert(Self::spec_bulbs_on(m) <= Self::spec_bulbs_on(mid));
            assert(Self::spec_bulbs_on(m) < k);
        }
    }

    proof fn lemma_exec_sqrt_matches_spec(x: u64, r: u64)
        requires
            1 <= x <= 1_000_000_002_000_001_000u64,
            r * r <= x,
            x < (r + 1) * (r + 1),
            r <= 2_000_000_000u64,
        ensures
            r as int == Self::spec_floor_sqrt(x as int),
    {
        let xi = x as int;
        let ri = r as int;
        Self::lemma_spec_sqrt_bounds(xi);
        let s = Self::spec_floor_sqrt(xi);
        Self::lemma_unique_sqrt(xi, ri, s);
        assert(ri == s);
    }
}

}
