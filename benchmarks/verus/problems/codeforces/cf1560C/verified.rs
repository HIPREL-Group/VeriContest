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

    proof fn lemma_exec_floor_sqrt_u64_matches_spec(ku: u64, f: u64)
        requires
            1 <= ku <= 1_000_000_000u64,
            0 <= f <= 31622u64,
            f * f <= ku,
            ku < (f + 1) * (f + 1),
        ensures
            f as int == Self::spec_floor_sqrt(ku as int),
    {
        let ni = ku as int;
        let fi = f as int;
        Self::lemma_spec_sqrt_bounds(ni);
        let s = Self::spec_floor_sqrt(ni);
        Self::lemma_unique_sqrt(ni, fi, s);
        assert(fi == s);
    }

    proof fn lemma_i64_u64_same_int(k: i64)
        requires
            1 <= k <= 1_000_000_000,
        ensures
            (k as u64) as int == k as int,
    {
    }

    proof fn lemma_spec_ceil_from_floor(k: int, f: int, s: int)
        requires
            k >= 1,
            f == Self::spec_floor_sqrt(k),
            (f * f == k && s == f) || (f * f != k && s == f + 1),
        ensures
            s == Self::spec_ceil_sqrt(k),
    {
        let t = Self::spec_ceil_sqrt(k);
        if f * f == k {
            assert(s == f);
            assert(t == f);
            assert(s == t);
        } else {
            assert(s == f + 1);
            assert(t == f + 1);
            assert(s == t);
        }
    }

    proof fn lemma_ceil_sqrt_shell(k: int)
        requires
            k >= 1,
        ensures
            ({
                let s = Self::spec_ceil_sqrt(k);
                (s - 1) * (s - 1) < k && k <= s * s
            }),
    {
        Self::lemma_spec_sqrt_bounds(k);
        let f = Self::spec_floor_sqrt(k);
        assert(f >= 0);
        let s = Self::spec_ceil_sqrt(k);
        if f * f == k {
            assert(s == f);
            assert(k == f * f);
            assert(k == s * s);
            assert(f * f >= 1);
            assert(f >= 1) by (nonlinear_arith)
                requires
                    f >= 0,
                    f * f >= 1,
            {
            }
            assert(s >= 1);
            assert((s - 1) * (s - 1) < s * s) by (nonlinear_arith)
                requires
                    s >= 1,
            {
            }
            assert((s - 1) * (s - 1) < k);
            assert(k <= s * s);
        } else {
            assert(s == f + 1);
            assert(f * f < k);
            assert((s - 1) * (s - 1) == f * f);
            assert((s - 1) * (s - 1) < k);
            assert(s * s == (f + 1) * (f + 1));
            assert(k < (f + 1) * (f + 1));
            assert(k <= s * s);
        }
    }

    proof fn lemma_off_bounds(k: int, s: int, off: int)
        requires
            k >= 1,
            s == Self::spec_ceil_sqrt(k),
            off == k - (s - 1) * (s - 1),
        ensures
            1 <= off && off <= 2 * s - 1,
    {
        Self::lemma_ceil_sqrt_shell(k);
        assert((s - 1) * (s - 1) < k);
        assert(k <= s * s);
        assert(s >= 1) by {
            if s <= 0 {
                assert(k <= s * s);
                assert((s - 1) * (s - 1) < k);
                assert(false) by (nonlinear_arith)
                    requires
                        s <= 0,
                        k >= 1,
                        k <= s * s,
                        (s - 1) * (s - 1) < k,
                {
                }
            }
        }
        assert(off >= 1);
        assert(off <= s * s - (s - 1) * (s - 1));
        assert(s * s - (s - 1) * (s - 1) == 2 * s - 1) by (nonlinear_arith)
            requires
                s >= 1,
        {
        }
        assert(off <= 2 * s - 1);
    }

    proof fn lemma_branch_matches_spec(k: int, s: int, off: int, r: int, c: int)
        requires
            k >= 1,
            s == Self::spec_ceil_sqrt(k),
            off == k - (s - 1) * (s - 1),
            (off <= s && r == off && c == s) || (off > s && r == s && c == 2 * s - off),
        ensures
            r == Self::spec_infinity_table_row(k) && c == Self::spec_infinity_table_col(k),
    {
        if off <= s {
            assert(r == off && c == s);
            assert(Self::spec_infinity_table_row(k) == off);
            assert(Self::spec_infinity_table_col(k) == s);
        } else {
            assert(r == s && c == 2 * s - off);
            assert(Self::spec_infinity_table_row(k) == s);
            assert(Self::spec_infinity_table_col(k) == 2 * s - off);
        }
    }

    pub fn infinity_table_cell(k: i64) -> (res: (i64, i64))
        requires
            1 <= k <= 1_000_000_000,
        ensures
            res.0 as int == Self::spec_infinity_table_row(k as int),
            res.1 as int == Self::spec_infinity_table_col(k as int),
    {
        let ku = k as u64;
        proof {
            Self::lemma_i64_u64_same_int(k);
            assert(ku as int == k as int);
        }
        let mut lo = 1u64;
        let mut hi = 1_000_000_001u64;
        while lo < hi
            invariant
                1 <= k <= 1_000_000_000,
                ku == k as u64,
                1 <= ku <= 1_000_000_000,
                1u64 <= lo <= hi <= 1_000_000_001u64,
                (lo - 1) * (lo - 1) <= ku,
                ku < hi * hi,
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
                assert(mid <= 1_000_000_000u64) by (nonlinear_arith)
                    requires
                        mid < hi,
                        hi <= 1_000_000_001u64,
                {
                }
            }
            proof {
                assert(mid * mid <= 1_000_000_002_000_000_001u64) by (nonlinear_arith)
                    requires
                        mid <= 1_000_000_000u64,
                {
                }
            }
            if mid * mid <= ku {
                lo = mid + 1;
                proof {
                    assert((lo - 1) == mid);
                    assert((lo - 1) * (lo - 1) <= ku);
                }
            } else {
                hi = mid;
                proof {
                    assert(ku < hi * hi);
                }
            }
        }
        let fu = lo - 1;
        proof {
            assert(lo == hi);
            assert(0 <= fu) by (nonlinear_arith)
                requires
                    lo >= 1,
                    fu == lo - 1,
                {
                }
            assert(fu <= 31622u64) by (nonlinear_arith)
                requires
                    lo <= 1_000_000_001u64,
                    fu == lo - 1,
                    (lo - 1) * (lo - 1) <= ku,
                    ku <= 1_000_000_000u64,
                {
                }
            assert(fu * fu <= ku);
            assert(ku < (fu + 1) * (fu + 1));
            Self::lemma_exec_floor_sqrt_u64_matches_spec(ku, fu);
        }
        let f = fu as i64;
        proof {
            assert(f as int == fu as int);
            assert(f as int == Self::spec_floor_sqrt(k as int));
        }
        let s = if f * f == k {
            f
        } else {
            f + 1
        };
        proof {
            Self::lemma_spec_ceil_from_floor(k as int, f as int, s as int);
            assert(s as int == Self::spec_ceil_sqrt(k as int));
            Self::lemma_ceil_sqrt_shell(k as int);
        }
        let prev = (s - 1) * (s - 1);
        let off = k - prev;
        proof {
            assert(prev as int == (s as int - 1) * (s as int - 1));
            assert(off as int == k as int - (s as int - 1) * (s as int - 1));
            Self::lemma_off_bounds(k as int, Self::spec_ceil_sqrt(k as int), off as int);
            assert(off as int <= 2 * s as int - 1);
        }
        if off <= s {
            proof {
                assert(off as int <= s as int);
                Self::lemma_branch_matches_spec(
                    k as int,
                    Self::spec_ceil_sqrt(k as int),
                    off as int,
                    off as int,
                    s as int,
                );
            }
            (off, s)
        } else {
            proof {
                assert(off as int > s as int);
                assert((2 * s - off) as int == 2 * s as int - off as int);
                Self::lemma_branch_matches_spec(
                    k as int,
                    Self::spec_ceil_sqrt(k as int),
                    off as int,
                    s as int,
                    (2 * s - off) as int,
                );
            }
            (s, 2 * s - off)
        }
    }
}

}
