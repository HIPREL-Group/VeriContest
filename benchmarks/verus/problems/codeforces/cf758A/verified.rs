use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_max_of(a: Seq<i32>, n: int) -> int
    recommends 1 <= n <= a.len(),
    decreases n,
{
    if n <= 1 {
        a[0] as int
    } else {
        let m = spec_max_of(a, n - 1);
        if (a[n - 1] as int) > m {
            a[n - 1] as int
        } else {
            m
        }
    }
}

pub open spec fn spec_gap_sum(a: Seq<i32>, n: int, maxv: int) -> int
    recommends 0 <= n <= a.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_gap_sum(a, n - 1, maxv) + (maxv - (a[n - 1] as int))
    }
}

pub open spec fn spec_holiday_equality(a: Seq<i32>, n: int) -> int
    recommends 1 <= n <= a.len(),
{
    let m = spec_max_of(a, n);
    spec_gap_sum(a, n, m)
}

proof fn lemma_spec_max_of_le_upper(a: Seq<i32>, n: int, cap: int)
    requires
        1 <= n <= a.len(),
        forall|t: int| 0 <= t < n ==> (a[t] as int) <= cap,
    ensures
        spec_max_of(a, n) <= cap,
    decreases n,
{
    if n <= 1 {
        reveal_with_fuel(spec_max_of, 2);
        assert(spec_max_of(a, 1) == a[0] as int);
        assert((a[0] as int) <= cap);
    } else {
        lemma_spec_max_of_le_upper(a, n - 1, cap);
        reveal_with_fuel(spec_max_of, 3);
        assert((a[n - 1] as int) <= cap);
    }
}

proof fn lemma_spec_max_of_next(a: Seq<i32>, i: int)
    requires
        1 <= i < a.len(),
    ensures
        spec_max_of(a, i + 1) == if (a[i] as int) > spec_max_of(a, i) {
            a[i] as int
        } else {
            spec_max_of(a, i)
        },
{
    reveal_with_fuel(spec_max_of, 20);
}

proof fn lemma_gap_sum_step(a: Seq<i32>, j: int, maxv: int)
    requires
        0 <= j < a.len(),
    ensures
        spec_gap_sum(a, j + 1, maxv) == spec_gap_sum(a, j, maxv) + (maxv - (a[j] as int)),
{
    reveal_with_fuel(spec_gap_sum, 20);
}

proof fn lemma_spec_max_ge_each(a: Seq<i32>, n: int, k: int)
    requires
        1 <= n <= a.len(),
        0 <= k < n,
    ensures
        spec_max_of(a, n) >= a[k] as int,
    decreases n,
{
    if n <= 1 {
        assert(k == 0);
        reveal_with_fuel(spec_max_of, 2);
        assert(spec_max_of(a, 1) == a[0] as int);
    } else {
        reveal_with_fuel(spec_max_of, 3);
        if k == n - 1 {
            assert(spec_max_of(a, n) >= a[k] as int);
        } else {
            lemma_spec_max_ge_each(a, n - 1, k);
            assert(spec_max_of(a, n) >= spec_max_of(a, n - 1));
            assert(spec_max_of(a, n - 1) >= a[k] as int);
        }
    }
}

proof fn lemma_gap_sum_nonneg(a: Seq<i32>, n: int, maxv: int)
    requires
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> (a[i] as int) <= maxv,
    ensures
        spec_gap_sum(a, n, maxv) >= 0,
    decreases n,
{
    if n <= 0 {
        reveal_with_fuel(spec_gap_sum, 1);
    } else {
        lemma_gap_sum_nonneg(a, n - 1, maxv);
        assert((a[n - 1] as int) <= maxv);
        reveal_with_fuel(spec_gap_sum, 2);
    }
}

proof fn lemma_gap_sum_ge_term(a: Seq<i32>, n: int, m: int, k: int)
    requires
        1 <= n <= a.len(),
        0 <= k < n,
        forall|i: int| 0 <= i < n ==> (a[i] as int) <= m,
    ensures
        spec_gap_sum(a, n, m) >= m - (a[k] as int),
    decreases n,
{
    if n == 1 {
        assert(k == 0);
        reveal_with_fuel(spec_gap_sum, 2);
        assert(spec_gap_sum(a, 1, m) == m - (a[0] as int));
    } else {
        reveal_with_fuel(spec_gap_sum, 3);
        if k == n - 1 {
            lemma_gap_sum_nonneg(a, n - 1, m);
            assert(spec_gap_sum(a, n, m) == spec_gap_sum(a, n - 1, m) + (m - (a[n - 1] as int)));
            assert(spec_gap_sum(a, n - 1, m) >= 0);
            assert(spec_gap_sum(a, n, m) >= m - (a[k] as int));
        } else {
            lemma_gap_sum_ge_term(a, n - 1, m, k);
            assert((a[n - 1] as int) <= m);
            lemma_gap_sum_nonneg(a, n - 1, m);
            assert(spec_gap_sum(a, n, m) >= spec_gap_sum(a, n - 1, m));
            assert(spec_gap_sum(a, n - 1, m) >= m - (a[k] as int));
        }
    }
}

impl Solution {
    pub fn holiday_equality_burles(n: usize, a: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 100,
            n == a.len(),
            forall|k: int|
                0 <= k < n as int ==> 0 <= #[trigger] a[k] <= 1_000_000,
        ensures
            res as int == spec_holiday_equality(a@, n as int),
    {
        let mut maxv = a[0];
        let mut i = 1usize;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 100,
                forall|k: int|
                    0 <= k < n as int ==> 0 <= #[trigger] a[k] <= 1_000_000,
                1 <= i <= n,
                maxv as int == spec_max_of(a@, i as int),
            decreases
                n - i,
        {
            proof {
                lemma_spec_max_of_next(a@, i as int);
            }
            if a[i] > maxv {
                maxv = a[i];
            }
            i += 1;
            proof {
                assert(maxv as int == spec_max_of(a@, i as int));
            }
        }
        proof {
            assert(i == n);
            assert(maxv as int == spec_max_of(a@, n as int));
        }
        let mut sum = 0i32;
        let mut j = 0usize;
        while j < n
            invariant
                n == a.len(),
                1 <= n <= 100,
                forall|k: int|
                    0 <= k < n as int ==> 0 <= #[trigger] a[k] <= 1_000_000,
                j <= n,
                maxv as int == spec_max_of(a@, n as int),
                sum as int == spec_gap_sum(a@, j as int, maxv as int),
                sum as int <= (j as int) * 1_000_000,
            decreases
                n - j,
        {
            proof {
                lemma_gap_sum_step(a@, j as int, maxv as int);
                assert(forall|t: int|
                    0 <= t < n as int ==> (a@[t] as int) <= maxv as int) by {
                    assert(maxv as int == spec_max_of(a@, n as int));
                    assert forall|t: int|
                        0 <= t < n as int implies (a@[t] as int) <= maxv as int by {
                        lemma_spec_max_ge_each(a@, n as int, t);
                    };
                };
                lemma_spec_max_ge_each(a@, n as int, j as int);
                assert(maxv as int >= (a@[j as int] as int));
                lemma_spec_max_of_le_upper(a@, n as int, 1_000_000);
                assert(maxv as int <= 1_000_000);
                assert((a@[j as int] as int) >= 0);
                assert((maxv as int - (a@[j as int] as int)) <= 1_000_000);
                assert((sum as int) + (maxv as int - (a@[j as int] as int))
                    <= ((j + 1) as int) * 1_000_000);
                assert(((j + 1) as int) * 1_000_000 <= 100 * 1_000_000);
                assert((sum as int) + (maxv as int - (a@[j as int] as int)) <= 100 * 1_000_000);
                assert(-2147483648 <= (sum as int) + (maxv as int - (a@[j as int] as int)));
                assert((sum as int) + (maxv as int - (a@[j as int] as int)) < 2147483648);
            }
            sum += maxv - a[j];
            j += 1;
            proof {
                assert(sum as int == spec_gap_sum(a@, j as int, maxv as int));
            }
        }
        proof {
            assert(j == n);
            assert(sum as int == spec_gap_sum(a@, n as int, maxv as int));
            assert(spec_holiday_equality(a@, n as int) == spec_gap_sum(a@, n as int, maxv as int));
            assert(sum as int == spec_holiday_equality(a@, n as int));
            assert forall|k: int|
                0 <= k < n as int implies spec_max_of(a@, n as int) >= a@[k] by {
                lemma_spec_max_ge_each(a@, n as int, k);
            };
            assert forall|k: int|
                0 <= k < n as int implies (sum as int) >= (spec_max_of(a@, n as int) - a@[k]) by {
                lemma_gap_sum_ge_term(a@, n as int, maxv as int, k);
                assert(maxv as int == spec_max_of(a@, n as int));
            };
        }
        sum
    }
}

}
