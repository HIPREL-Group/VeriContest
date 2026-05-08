use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn total_sum(a: Seq<i64>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::total_sum(a, end - 1) + a[end - 1] as int
        }
    }

    pub open spec fn square_of(s: int) -> int {
        s * s
    }

    pub open spec fn is_perfect_square(val: int) -> bool {
        exists |s: int| 0 <= s && #[trigger] Self::square_of(s) == val
    }

    proof fn lemma_total_sum_bounds(a: Seq<i64>, end: int)
        requires
            0 <= end <= a.len(),
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
        ensures
            end <= Self::total_sum(a, end) <= 1_000_000_000 * end,
        decreases end,
    {
        if end > 0 {
            Self::lemma_total_sum_bounds(a, end - 1);
        }
    }

    proof fn lemma_sqrt_monotone(a: int, b: int)
        requires
            0 <= a <= b,
        ensures
            a * a <= b * b,
    {
        assert(a * a <= b * b) by (nonlinear_arith)
            requires 0 <= a, a <= b;
    }

    proof fn lemma_sqrt_unique(s1: int, s2: int)
        requires
            0 <= s1,
            0 <= s2,
            s1 * s1 == s2 * s2,
        ensures
            s1 == s2,
    {
        if s1 < s2 {
            Self::lemma_sqrt_monotone(s1, s2);
            assert(s1 * s1 < s2 * s2) by (nonlinear_arith)
                requires 0 <= s1, s1 < s2;
        } else if s1 > s2 {
            Self::lemma_sqrt_monotone(s2, s1);
            assert(s2 * s2 < s1 * s1) by (nonlinear_arith)
                requires 0 <= s2, s2 < s1;
        }
    }

    proof fn lemma_no_square_between(lo: int, val: int)
        requires
            lo >= 0,
            lo * lo <= val,
            (lo + 1) * (lo + 1) > val,
        ensures
            Self::is_perfect_square(val) == (lo * lo == val),
    {
        if lo * lo == val {
            assert(Self::is_perfect_square(val)) by {
                assert(0 <= lo && Self::square_of(lo) == val);
            };
        } else {
            assert(lo * lo < val);
            assert(!Self::is_perfect_square(val)) by {
                assert forall |s: int| 0 <= s && #[trigger] Self::square_of(s) == val implies false by {
                    if s <= lo {
                        Self::lemma_sqrt_monotone(s, lo);
                        assert(Self::square_of(s) <= Self::square_of(lo));
                        assert(Self::square_of(s) < val);
                    } else {
                        assert(s >= lo + 1);
                        Self::lemma_sqrt_monotone(lo + 1, s);
                        assert(Self::square_of(s) >= Self::square_of(lo + 1));
                        assert(Self::square_of(s) > val);
                    }
                };
            };
        }
    }

    pub fn can_square(a: Vec<i64>) -> (result: bool)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
        ensures
            result == Self::is_perfect_square(Self::total_sum(a@, a@.len() as int)),
    {
        let n = a.len();
        let ghost orig = a@;
        let ghost sum_spec = Self::total_sum(orig, n as int);

        let mut total: i64 = 0;
        let mut k: usize = 0;
        while k < n
            invariant
                n == a.len(),
                a@ == orig,
                0 <= k <= n,
                n <= 200_000,
                forall |kk: int| 0 <= kk < n ==> 1 <= #[trigger] orig[kk] <= 1_000_000_000,
                total as int == Self::total_sum(orig, k as int),
                k as int <= total as int <= 1_000_000_000 * k as int,
            decreases n - k,
        {
            proof {
                Self::lemma_total_sum_bounds(orig, k as int + 1);
            }
            total = total + a[k];
            k = k + 1;
        }

        proof {
            assert(total as int == sum_spec);
        }

        let mut lo: i64 = 0;
        let mut hi: i64 = 15_000_000;

        proof {
            Self::lemma_total_sum_bounds(orig, n as int);
            assert(sum_spec <= 200_000_000_000_000int);
            assert(15_000_000int * 15_000_000 >= 200_000_000_000_000int) by (nonlinear_arith);
        }

        while lo < hi
            invariant
                0 <= lo <= hi,
                hi <= 15_000_000,
                total as int == sum_spec,
                total >= 1,
                lo == 0 || Self::square_of(lo as int - 1) < total as int,
                Self::square_of(hi as int) >= total as int,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;

            proof {
                assert(0 <= mid as int <= 15_000_000int);
                assert(Self::square_of(mid as int) >= 0) by {
                    assert(mid as int * mid as int >= 0) by (nonlinear_arith)
                        requires mid as int >= 0;
                };
                assert(Self::square_of(mid as int) <= Self::square_of(15_000_000int)) by {
                    Self::lemma_sqrt_monotone(mid as int, 15_000_000int);
                };
                assert(Self::square_of(15_000_000int) == 225_000_000_000_000int) by (nonlinear_arith);
                assert(mid as int * mid as int <= 225_000_000_000_000int) by (nonlinear_arith)
                    requires 0 <= mid as int, mid as int <= 15_000_000int;
            }

            if mid * mid < total {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        proof {
            assert(lo == hi);
            assert(Self::square_of(lo as int) >= sum_spec);
            if lo > 0 {
                assert(Self::square_of(lo as int - 1) < sum_spec);
            }
            if Self::square_of(lo as int) == sum_spec {
                assert(lo as int * lo as int == sum_spec);
                assert(0 <= lo as int && Self::square_of(lo as int) == sum_spec);
            } else {
                assert(Self::square_of(lo as int) > sum_spec);
                assert(lo > 0) by {
                    if lo <= 0 {
                        assert(lo == 0);
                        assert(Self::square_of(lo as int) == 0);
                        assert(sum_spec >= 1);
                        assert(0 > 1);
                    }
                };
                let isqrt = lo as int - 1;
                assert(isqrt >= 0);
                assert(Self::square_of(isqrt) < sum_spec);
                assert(Self::square_of(isqrt + 1) > sum_spec);
                Self::lemma_no_square_between(isqrt, sum_spec);
            }
            assert(lo as int <= 15_000_000int);
            assert(lo as int * lo as int <= 225_000_000_000_000int) by (nonlinear_arith)
                requires 0 <= lo as int, lo as int <= 15_000_000int;
        }

        lo * lo == total
    }
}

}
