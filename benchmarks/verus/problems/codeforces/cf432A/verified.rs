use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_eligible_threshold(k: int) -> int {
    5 - k
}

pub open spec fn spec_is_eligible(y: int, k: int) -> bool {
    y <= spec_eligible_threshold(k)
}

pub open spec fn spec_count_eligible(s: Seq<i64>, n: int, k: int) -> int
    recommends 0 <= n <= s.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_count_eligible(s, n - 1, k)
            + if spec_is_eligible(s[n - 1] as int, k) {
                1int
            } else {
                0int
            }
    }
}

proof fn lemma_spec_count_eligible_step(s: Seq<i64>, i: int, k: int)
    requires
        0 <= i < s.len(),
        1 <= k <= 5,
        forall|t: int| 0 <= t < s.len() ==> 0 <= #[trigger] s[t] <= 5,
    ensures
        spec_count_eligible(s, i + 1, k)
            == spec_count_eligible(s, i, k)
                + if spec_is_eligible(s[i] as int, k) {
                    1int
                } else {
                    0int
                },
{
    reveal_with_fuel(spec_count_eligible, 10);
}

proof fn lemma_spec_count_eligible_nonneg(s: Seq<i64>, n: int, k: int)
    requires
        0 <= n <= s.len(),
    ensures
        spec_count_eligible(s, n, k) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_spec_count_eligible_nonneg(s, n - 1, k);
        reveal_with_fuel(spec_count_eligible, 2);
    } else {
        reveal_with_fuel(spec_count_eligible, 1);
    }
}

proof fn lemma_five_minus_k_int(k: i32)
    requires
        1 <= (k as int) <= 5,
    ensures
        ((5 - k) as i64 as int) == (5 - k as int),
{
    assert(0 <= 5 - k <= 4);
}

proof fn lemma_cmp_matches_spec(yv: int, kv: int)
    requires
        1 <= kv <= 5,
        0 <= yv <= 5,
    ensures
        (yv <= 5 - kv) == spec_is_eligible(yv, kv),
{
    assert(spec_eligible_threshold(kv) == 5 - kv);
}

proof fn lemma_int_div_forall(c: int, r: int)
    requires
        c >= 0,
        r == c / 3,
    ensures
        forall|m: int|
            (0 <= m && #[trigger] (m * 3) <= c) ==> m <= r,
{
    assert forall|m: int|
        (0 <= m && #[trigger] (m * 3) <= c) implies m <= r by {
        if (0 <= m && (m * 3) <= c) {
            assert(m * 3 <= c);
            assert(m <= c / 3) by (nonlinear_arith)
                requires
                    m * 3 <= c,
                    c >= 0,
                    m >= 0,
            ;
            assert(r == c / 3);
            assert(m <= r);
        }
    };
}

impl Solution {
    pub fn max_teams(n: usize, k: i32, y: Vec<i64>) -> (result: i32)
        requires
            1 <= n <= 2000,
            n == y.len(),
            1 <= (k as int) <= 5,
            forall|i: int|
                0 <= i < n as int ==> 0 <= (#[trigger] y[i] as int) <= 5,
        ensures
            result as int == spec_count_eligible(y@, n as int, k as int) / 3,
    {
        proof {
            assert(1 <= (k as int) <= 5);
        }
        let mut cnt: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == y.len(),
                0 <= i <= n,
                1 <= (k as int) <= 5,
                forall|u: int|
                    0 <= u < n as int ==> 0 <= (#[trigger] y[u] as int) <= 5,
                (cnt as int) <= (i as int),
                (cnt as int) <= (n as int),
                (cnt as int) == spec_count_eligible(y@, i as int, k as int),
            decreases n - i,
        {
            proof {
                assert((i as int) < (n as int));
                assert((i as int) < (y@.len() as int));
                lemma_spec_count_eligible_nonneg(y@, i as int, k as int);
            }
            if y[i] <= (5 - k) as i64 {
                proof {
                    assert(0 <= (i as int) && (i as int) < (n as int));
                    assert((y@[i as int] as int) >= 0 && (y@[i as int] as int) <= 5);
                    assert(y@[i as int] == y[i as int]);
                    assert(y[i as int] <= (5 - k) as i64);
                    lemma_five_minus_k_int(k);
                    assert((y[i as int] as int) <= ((5 - k) as i64 as int));
                    assert((y[i as int] as int) <= 5 - k as int);
                    lemma_cmp_matches_spec(y[i as int] as int, k as int);
                    assert(spec_is_eligible(y[i as int] as int, k as int));
                    lemma_spec_count_eligible_step(y@, i as int, k as int);
                    assert(spec_count_eligible((y@), (i + 1) as int, k as int) == spec_count_eligible((y@), i as int, k as int) + 1);
                }
                cnt = cnt + 1;
            } else {
                proof {
                    assert(0 <= (i as int) && (i as int) < (n as int));
                    assert((y@[i as int] as int) >= 0 && (y@[i as int] as int) <= 5);
                    assert(y@[i as int] == y[i as int]);
                    assert(!(y[i as int] <= (5 - k) as i64));
                    lemma_five_minus_k_int(k);
                    assert(!((y[i as int] as int) <= ((5 - k) as i64 as int)));
                    assert(!((y[i as int] as int) <= 5 - k as int));
                    lemma_cmp_matches_spec(y[i as int] as int, k as int);
                    assert(!spec_is_eligible(y[i as int] as int, k as int));
                    lemma_spec_count_eligible_step(y@, i as int, k as int);
                    assert(spec_count_eligible((y@), (i + 1) as int, k as int) == spec_count_eligible((y@), i as int, k as int));
                }
            }
            i = i + 1;
            proof {
                assert((cnt as int) == spec_count_eligible(y@, i as int, k as int));
            }
        }
        proof {
            lemma_spec_count_eligible_nonneg(y@, n as int, k as int);
            assert((cnt as int) == spec_count_eligible((y@), n as int, k as int));
            assert(((cnt / 3) as i32) as int == spec_count_eligible((y@), n as int, k as int) / 3);
            lemma_int_div_forall(spec_count_eligible((y@), n as int, k as int), (cnt / 3) as int);
        }
        (cnt / 3) as i32
    }
}

}
