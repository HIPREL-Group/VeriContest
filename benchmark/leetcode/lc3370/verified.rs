use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_strictly_increases, lemma_pow2_unfold, pow2};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_all_set_bits(x: int) -> bool {
        x > 0 && exists|k: nat| x == pow2(k) - 1
    }

    pub fn smallest_number(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            n <= result,
            Self::is_all_set_bits(result as int),
            forall|m: int| n as int <= m < result as int ==> !(#[trigger] Self::is_all_set_bits(m)),
    {
        let target = n + 1;
        let mut p = 1;
        let ghost mut exp: nat = 0;

        proof {
            lemma2_to64();
            assert(p as int == pow2(exp));
        }

        while p < target
            invariant
                1 <= n <= 1000,
                target == n + 1,
                2 <= target <= 1001,
                1 <= p <= 2000,
                p as int == pow2(exp),
                forall|j: nat| j < exp ==> #[trigger] pow2(j) < target as int,
            decreases 2001 - p,
        {
            let old_p = p;
            let ghost old_exp = exp;
            p = p * 2;
            proof {
                exp = old_exp + 1;
                lemma_pow2_unfold(old_exp + 1);
                assert(pow2(old_exp + 1) == 2 * pow2(old_exp));
                assert(old_p as int == pow2(old_exp));
                assert(p as int == 2 * old_p as int);
                assert(p as int == pow2(exp));
                assert(old_p < target);
                assert(old_p <= 1000);
                assert(1 <= old_p);
                assert(1 <= p <= 2000) by (nonlinear_arith)
                    requires
                        p as int == 2 * old_p as int,
                        1 <= old_p,
                        old_p <= 1000,
                {
                }
                assert forall|j: nat| j < exp implies #[trigger] pow2(j) < target as int by {
                    if j < old_exp {
                    } else {
                        assert(j == old_exp);
                        assert(pow2(j) == old_p as int);
                        assert(old_p < target);
                    }
                }
                assert(p > old_p) by (nonlinear_arith)
                    requires
                        p as int == 2 * old_p as int,
                        old_p >= 1,
                {
                }
            }
        }

        let r = p - 1;
        proof {
            assert(p >= target);
            assert(r as int == p as int - 1);
            assert(n as int <= r as int) by (nonlinear_arith)
                requires
                    p as int >= target as int,
                    target as int == n as int + 1,
                    r as int == p as int - 1,
            {
            }
            assert(r as int > 0) by (nonlinear_arith)
                requires
                    n as int <= r as int,
                    n >= 1,
            {
            }

            assert(Self::is_all_set_bits(r as int)) by {
                assert(r as int == pow2(exp) - 1) by (nonlinear_arith)
                    requires
                        p as int == pow2(exp),
                        r as int == p as int - 1,
                {
                }
                assert(r as int > 0);
            }

            assert forall|m: int| n as int <= m < r as int implies !(#[trigger] Self::is_all_set_bits(m)) by {
                if Self::is_all_set_bits(m) {
                    let k: nat = choose|kk: nat| m == pow2(kk) - 1;
                    assert(m + 1 == pow2(k));
                    assert(m + 1 < p as int) by (nonlinear_arith)
                        requires
                            m < r as int,
                            r as int == p as int - 1,
                    {
                    }
                    assert(pow2(k) < pow2(exp));

                    if k == exp {
                        assert(pow2(k) == pow2(exp));
                        assert(false);
                    }

                    if exp < k {
                        lemma_pow2_strictly_increases(exp, k);
                        assert(pow2(exp) < pow2(k));
                        assert(false);
                    }

                    assert(k < exp);
                    assert(pow2(k) < target as int);
                    assert(target as int <= m + 1) by (nonlinear_arith)
                        requires
                            n as int <= m,
                            target as int == n as int + 1,
                    {
                    }
                    assert(pow2(k) >= target as int);
                    assert(false);
                }
            }
        }
        p - 1
    }
}

}
