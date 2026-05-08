use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn pow2_int(e: int) -> int
    decreases e,
{
    if e <= 0 {
        1
    } else {
        2 * pow2_int(e - 1)
    }
}

pub open spec fn min_balance_answer(n: int) -> int {
    pow2_int(n / 2 + 1) - 2
}

proof fn lemma_pow2_int_nonneg(e: int)
    requires
        e >= 0,
    ensures
        pow2_int(e) >= 1,
    decreases e,
{
    if e <= 0 {
    } else {
        lemma_pow2_int_nonneg(e - 1);
        assert(pow2_int(e) == 2 * pow2_int(e - 1));
        assert(pow2_int(e - 1) >= 1);
        assert(pow2_int(e) >= 2);
    }
}

proof fn lemma_pow2_step(k: int)
    requires
        k >= 0,
    ensures
        pow2_int(k + 1) == 2 * pow2_int(k),
{
    assert(k + 1 > 0);
    assert(pow2_int(k + 1) == 2 * pow2_int((k + 1) - 1));
    assert((k + 1) - 1 == k);
}

proof fn lemma_pow2_int_le(k: int, m: int)
    requires
        0 <= k <= m,
    ensures
        pow2_int(k) <= pow2_int(m),
    decreases m - k,
{
    if k == m {
    } else {
        assert(k < m);
        lemma_pow2_int_nonneg(k);
        lemma_pow2_int_nonneg(m - 1);
        lemma_pow2_int_le(k, m - 1);
        assert(pow2_int(m) == 2 * pow2_int(m - 1));
        assert(pow2_int(k) <= pow2_int(m - 1));
        assert(pow2_int(m - 1) <= 2 * pow2_int(m - 1));
        assert(pow2_int(k) <= pow2_int(m));
    }
}

pub struct Solution;

impl Solution {
    pub fn phoenix_balance_min_diff(n: i32) -> (result: i64)
        requires
            2 <= n <= 30,
            (n as int) % 2 == 0,
        ensures
            result as int == min_balance_answer(n as int),
            exists|e: int|
                e == (n as int) / 2 + 1 && result as int == #[trigger] pow2_int(e) - 2,
    {
        let half = n / 2;
        let exp = half + 1;
        proof {
            assert(2 <= (n as int) <= 30);
            assert((n as int) % 2 == 0);
            assert((half as int) == (n as int) / 2);
            assert(1 <= (half as int) <= 15);
            assert((exp as int) == (half as int) + 1);
            assert((exp as int) == (n as int) / 2 + 1);
            lemma_pow2_int_nonneg((exp as int));
        }
        let mut p = 1i64;
        let mut k = 0i32;
        proof {
            assert(p as int == pow2_int(0));
            assert((k as int) == 0);
        }
        while k < exp
            invariant
                2 <= n <= 30,
                (n as int) % 2 == 0,
                half == n / 2,
                exp == half + 1,
                0 <= k <= exp,
                p as int == pow2_int((k as int)),
                (k as int) <= (exp as int),
                (exp as int) <= 16,
                0 <= p <= 65536,
            decreases exp - k,
        {
            proof {
                assert((k as int) < (exp as int));
                assert((exp as int) <= 16);
                assert((k as int) <= 15);
                lemma_pow2_int_le((k as int), 15);
                assert(p as int == pow2_int((k as int)));
                assert(pow2_int((k as int)) <= pow2_int(15));
                assert((p as int) <= pow2_int(15));
                reveal_with_fuel(pow2_int, 20);
                assert(pow2_int(15) == 32768);
                assert((p as int) <= 32768);
                assert((p as int) * 2 <= 65536);
                assert((p as int) * 2 < 9223372036854775808);
                lemma_pow2_step((k as int));
                assert((p * 2) as int == 2 * pow2_int((k as int)));
                assert((p * 2) as int == pow2_int((k as int) + 1));
            }
            p = p * 2;
            k = k + 1;
            proof {
                assert(p as int == pow2_int((k as int)));
                assert((k as int) <= 16);
                lemma_pow2_int_le((k as int), 16);
                assert(pow2_int((k as int)) <= pow2_int(16));
                assert((p as int) <= 65536);
            }
        }
        proof {
            assert(k == exp);
            assert((k as int) == (exp as int));
            assert(p as int == pow2_int((exp as int)));
            assert((exp as int) == (n as int) / 2 + 1);
            assert(p as int == pow2_int((n as int) / 2 + 1));
            assert((p - 2) as int == pow2_int((n as int) / 2 + 1) - 2);
            assert((p - 2) as int == min_balance_answer(n as int));
            assert(exists|e: int|
                e == (n as int) / 2 + 1 && (p - 2) as int == #[trigger] pow2_int(e) - 2);
        }
        p - 2
    }
}

}
