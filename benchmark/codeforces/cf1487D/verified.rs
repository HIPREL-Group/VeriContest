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

    proof fn lemma_exec_sqrt_matches_spec(m: u64, r: u64)
        requires
            1 <= m <= 2_000_000_000u64,
            r * r <= m,
            m < (r + 1) * (r + 1),
            r <= 2_000_000_000u64,
        ensures
            r as int == Self::spec_floor_sqrt(m as int),
    {
        let mi = m as int;
        let ri = r as int;
        Self::lemma_spec_sqrt_bounds(mi);
        let s = Self::spec_floor_sqrt(mi);
        Self::lemma_unique_sqrt(mi, ri, s);
        assert(ri == s);
    }

    proof fn lemma_valid_implies_le_sqrt(n: int, a: int)
        requires
            n >= 1,
            is_valid_odd_a(n, a),
        ensures
            a <= Self::spec_floor_sqrt(2 * n - 1),
    {
        let m = 2 * n - 1;
        assert(3 <= a);
        assert(a % 2 == 1);
        assert(a * a + 1 <= 2 * n);
        assert(a * a <= 2 * n - 1) by (nonlinear_arith)
            requires
                a * a + 1 <= 2 * n,
            {
            }
        assert(a * a <= m);
        Self::lemma_spec_sqrt_bounds(m);
        let k = Self::spec_floor_sqrt(m);
        assert(k * k <= m);
        assert(m < (k + 1) * (k + 1));
        assert(a >= 0);
        if a > k {
            assert(a >= k + 1);
            assert(a * a >= (k + 1) * (k + 1)) by (nonlinear_arith)
                requires
                    a >= k + 1,
                    k >= 0,
                {
            }
            assert(a * a > m);
            assert(false);
        } else {
            assert(a <= k);
        }
    }

    proof fn lemma_le_sqrt_implies_valid(n: int, a: int)
        requires
            n >= 1,
            3 <= a,
            a % 2 == 1,
            a <= Self::spec_floor_sqrt(2 * n - 1),
        ensures
            is_valid_odd_a(n, a),
    {
        let m = 2 * n - 1;
        Self::lemma_spec_sqrt_bounds(m);
        let k = Self::spec_floor_sqrt(m);
        assert(a <= k);
        assert(k >= 0);
        assert(a >= 0);
        assert(a * a <= k * k) by (nonlinear_arith)
            requires
                0 <= a <= k,
                k >= 0,
            {
        }
        assert(k * k <= m);
        assert(a * a <= m) by (nonlinear_arith)
            requires
                a * a <= k * k,
                k * k <= m,
                a >= 0,
                k >= 0,
            {
        }
        assert(a * a + 1 <= 2 * n) by (nonlinear_arith)
            requires
                a * a <= 2 * n - 1,
            {
            }
    }

    proof fn lemma_spec_answer_from_k(n: int, k: int)
        requires
            n >= 1,
            k == Self::spec_floor_sqrt(2 * n - 1),
        ensures
            spec_answer(n)
                == if k < 3 {
                    0
                } else {
                    (k + 1) / 2 - 1
                },
    {
        let m = 2 * n - 1;
        assert(Self::spec_floor_sqrt(m) == k);
        assert(spec_answer(n) == if k < 3 { 0 } else { (k + 1) / 2 - 1 });
    }

    pub fn floor_sqrt_u64(m: u64) -> (r: u64)
        requires
            1 <= m <= 2_000_000_000u64,
        ensures
            r as int == Self::spec_floor_sqrt(m as int),
            r <= 2_000_000_000u64,
    {
        let mut lo = 1u64;
        let mut hi = 2_000_000_001u64;
        while lo < hi
            invariant
                1u64 <= m <= 2_000_000_000u64,
                1u64 <= lo <= hi <= 2_000_000_001u64,
                (lo - 1) * (lo - 1) <= m,
                m < hi * hi,
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
            if mid * mid <= m {
                lo = mid + 1;
                proof {
                    assert((lo - 1) == mid);
                    assert((lo - 1) * (lo - 1) <= m);
                }
            } else {
                hi = mid;
                proof {
                    assert(m < hi * hi);
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
            assert(r * r <= m);
            assert(m < (r + 1) * (r + 1));
            Self::lemma_exec_sqrt_matches_spec(m, r);
        }
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
        proof {
            assert forall|a: int| #[trigger] is_valid_odd_a(n as int, a) implies a
                <= Self::spec_floor_sqrt(2 * (n as int) - 1) by {
                assert forall|a: int| is_valid_odd_a(n as int, a) implies a
                    <= Self::spec_floor_sqrt(2 * (n as int) - 1) by {
                    assert(is_valid_odd_a(n as int, a));
                    Self::lemma_valid_implies_le_sqrt(n as int, a);
                }
            }
            assert forall|a: int| (3 <= a && a % 2 == 1 && a <= Self::spec_floor_sqrt(2 * (n as int) - 1)) implies is_valid_odd_a(
                n as int,
                a,
            ) by {
                assert(3 <= a && a % 2 == 1 && a <= Self::spec_floor_sqrt(2 * (n as int) - 1));
                Self::lemma_le_sqrt_implies_valid(n as int, a);
            }
        }
        let m = 2 * n - 1;
        proof {
            assert(m >= 1);
            assert(2 * n <= 2_000_000_000u64) by (nonlinear_arith)
                requires
                    n <= 1_000_000_000u64,
                {
                }
            assert(m == 2 * n - 1);
            assert(m <= 1_999_999_999u64) by (nonlinear_arith)
                requires
                    2 * n <= 2_000_000_000u64,
                    m == 2 * n - 1,
                {
                }
        }
        let k = Self::floor_sqrt_u64(m);
        proof {
            assert(k as int == Self::spec_floor_sqrt(m as int));
            assert(k as int == Self::spec_floor_sqrt(2 * (n as int) - 1));
            Self::lemma_spec_answer_from_k(n as int, k as int);
        }
        if k < 3 {
            proof {
                assert(spec_answer(n as int) == 0);
            }
            0
        } else {
            let res = (k + 1) / 2 - 1;
            proof {
                assert(spec_answer(n as int) == (k as int + 1) / 2 - 1);
                assert(res as int == spec_answer(n as int));
            }
            res
        }
    }
}

}
