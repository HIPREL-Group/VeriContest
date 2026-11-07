use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_additional(k: int, m: nat) -> int
    decreases m,
{
    if m == 0 {
        0
    } else {
        max_additional(k, (m - 1) as nat) + (k - m as int)
    }
}

proof fn lemma_max_additional_step(k: int, m: nat)
    requires
        2 <= k,
        m < k - 1,
    ensures
        max_additional(k, (m + 1) as nat) == max_additional(k, m) + (k - m as int - 1),
{
    reveal_with_fuel(max_additional, 2);
}

proof fn lemma_max_additional_monotone(k: int, a: nat, b: nat)
    requires
        2 <= k,
        a <= b < k,
    ensures
        max_additional(k, a) <= max_additional(k, b),
    decreases b - a,
{
    if a < b {
        lemma_max_additional_monotone(k, a, (b - 1) as nat);
        lemma_max_additional_step(k, (b - 1) as nat);
        assert(k - b as int >= 0);
    }
}

proof fn lemma_max_additional_formula(k: int, m: nat)
    requires
        2 <= k,
        m < k,
    ensures
        max_additional(k, m) == m as int * (2 * k - m as int - 1) / 2,
    decreases m,
{
    if m == 0 {
    } else {
        lemma_max_additional_formula(k, (m - 1) as nat);
        lemma_max_additional_step(k, (m - 1) as nat);
        assert(max_additional(k, (m - 1) as nat) == (m as int - 1) * (2 * k - m as int) / 2);
        assert(max_additional(k, m) == max_additional(k, (m - 1) as nat) + (k - m as int));
        assert(max_additional(k, m) == m as int * (2 * k - m as int - 1) / 2) by (nonlinear_arith)
            requires
                max_additional(k, (m - 1) as nat) == (m as int - 1) * (2 * k - m as int) / 2,
                max_additional(k, m) == max_additional(k, (m - 1) as nat) + (k - m as int),
                m > 0;
    }
}

impl Solution {
    fn max_additional_exec(k: i128, m: i128) -> (res: i128)
        requires
            2 <= k <= 1_000_000_000,
            0 <= m < k,
        ensures
            res as int == max_additional(k as int, m as nat),
    {
        proof {
            assert(0 <= m <= 999_999_999) by (nonlinear_arith)
                requires
                    2 <= k <= 1_000_000_000,
                    0 <= m < k;
            assert(1 <= 2 * k - m - 1 <= 1_999_999_999) by (nonlinear_arith)
                requires
                    2 <= k <= 1_000_000_000,
                    0 <= m < k;
            assert(m * (2 * k - m - 1) <= 2_000_000_000_000_000_000) by (nonlinear_arith)
                requires
                    0 <= m <= 999_999_999,
                    1 <= 2 * k - m - 1 <= 1_999_999_999;
            assert(m * (2 * k - m - 1) < 170141183460469231731687303715884105727) by (nonlinear_arith)
                requires
                    m * (2 * k - m - 1) <= 2_000_000_000_000_000_000;
        }
        let res = m * (2 * k - m - 1) / 2;
        proof {
            lemma_max_additional_formula(k as int, m as nat);
            assert(res == m * (2 * k - m - 1) / 2);
            assert(res as int == m as int * (2 * k as int - m as int - 1) / 2);
        }
        res
    }

    pub fn min_splitters(n: i128, k: i128) -> (res: i128)
        requires
            1 <= n <= 1_000_000_000_000_000_000,
            2 <= k <= 1_000_000_000,
        ensures
            n == 1 ==> res == 0,
            n > 1 && max_additional(k as int, (k - 1) as nat) < n as int - 1 ==> res == -1,
            n > 1 && max_additional(k as int, (k - 1) as nat) >= n as int - 1 ==> {
                1 <= res < k
                    && n as int - 1 <= max_additional(k as int, res as nat)
                    && forall|m: int| 0 <= m < res as int ==> #[trigger] max_additional(k as int, m as nat) < n as int - 1
            },
    {
        if n == 1 {
            return 0;
        }
        let need = n - 1;
        let total = Self::max_additional_exec(k, k - 1);
        if need > total {
            proof {
                assert forall|m: int| 0 <= m < k as int implies #[trigger] max_additional(k as int, m as nat) < n as int - 1 by {
                    if m == k as int - 1 {
                        assert(max_additional(k as int, m as nat) == max_additional(k as int, (k - 1) as nat));
                        assert(max_additional(k as int, (k - 1) as nat) == total as int);
                    } else {
                        lemma_max_additional_monotone(k as int, m as nat, (k - 1) as nat);
                        assert(max_additional(k as int, m as nat) <= max_additional(k as int, (k - 1) as nat));
                        assert(max_additional(k as int, (k - 1) as nat) == total as int);
                    }
                }
            }
            return -1;
        }
        let mut lo = 1i128;
        let mut hi = k - 1;
        while lo < hi
            invariant
                1 <= n <= 1_000_000_000_000_000_000,
                2 <= k <= 1_000_000_000,
                1 <= need,
                1 <= lo <= hi < k,
                need as int <= max_additional(k as int, hi as nat),
                lo == 1 || max_additional(k as int, (lo - 1) as nat) < need as int,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            proof {
                assert(lo <= mid < hi);
            }
            let max_mid = Self::max_additional_exec(k, mid);
            if max_mid >= need {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        proof {
            assert(lo == hi);
            assert(need as int <= max_additional(k as int, lo as nat));
            assert forall|m: int| 0 <= m < lo as int implies #[trigger] max_additional(k as int, m as nat) < n as int - 1 by {
                if lo == 1 {
                } else if m == lo as int - 1 {
                    assert(max_additional(k as int, m as nat) == max_additional(k as int, (lo - 1) as nat));
                    assert(max_additional(k as int, (lo - 1) as nat) < need as int);
                } else {
                    lemma_max_additional_monotone(k as int, m as nat, (lo - 1) as nat);
                    assert(max_additional(k as int, m as nat) <= max_additional(k as int, (lo - 1) as nat));
                    assert(max_additional(k as int, (lo - 1) as nat) < need as int);
                }
            }
        }
        lo
    }
}

}
