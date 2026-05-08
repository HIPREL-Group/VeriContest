use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_value(x: int) -> int {
        if x < 0 { -x } else { x }
    }

    pub open spec fn tri(n: int) -> int {
        n * (n + 1) / 2
    }

    pub open spec fn valid_steps(target_abs: int, n: int) -> bool {
        0 <= target_abs
            && 0 <= n
            && Self::tri(n) >= target_abs
            && (Self::tri(n) - target_abs) % 2 == 0
    }

    proof fn lemma_tri_nonnegative(n: int)
        requires
            0 <= n,
        ensures
            0 <= Self::tri(n),
            n <= Self::tri(n) + 1,
    {
        assert(0 <= n * (n + 1));
        assert(0 <= Self::tri(n));
        assert(2 * n <= n * (n + 1) + 2) by (nonlinear_arith)
            requires
                0 <= n,
        ;
        assert(n <= Self::tri(n) + 1) by (nonlinear_arith)
            requires
                2 * n <= n * (n + 1) + 2,
        ;
    }

    #[verifier::loop_isolation(false)]
    pub fn reach_number(target: i32) -> (res: i32)
        requires
            -1_000_000_000 <= target <= 1_000_000_000,
            target != 0,
        ensures
            Self::valid_steps(Self::abs_value(target as int), res as int),
            forall|m: int| 0 <= m < res as int ==> !#[trigger] Self::valid_steps(Self::abs_value(target as int), m),
    {
        let target_abs = if target < 0 { -target } else { target };
        proof {
            assert((target_abs as int) == Self::abs_value(target as int));
            assert(1 <= (target_abs as int) <= 1_000_000_000);
        }
        let mut step: i32 = 0;
        let mut sum: i32 = 0;

        while sum < target_abs
            invariant
                (target_abs as int) == Self::abs_value(target as int),
                1 <= (target_abs as int) <= 1_000_000_000,
                0 <= (step as int),
                (step as int) <= 50_000,
                (sum as int) == Self::tri(step as int),
                forall|m: int| 0 <= m < (step as int) ==> #[trigger] Self::tri(m) < (target_abs as int),
            decreases if (sum as int) < (target_abs as int) { (target_abs as int) - (sum as int) } else { 0int },
        {
            proof {
                assert((sum as int) < (target_abs as int));
                assert((step as int) < 50_000) by (nonlinear_arith)
                    requires
                        (sum as int) == Self::tri(step as int),
                        (sum as int) < (target_abs as int),
                        (target_abs as int) <= 1_000_000_000,
                ;
                assert((sum as int) + ((step as int) + 1) < (i32::MAX as int)) by (nonlinear_arith)
                    requires
                        (sum as int) < (target_abs as int),
                        (target_abs as int) <= 1_000_000_000,
                        (step as int) < 50_000,
                ;
            }
            let old_step = step;
            let old_sum = sum;
            step += 1;
            sum += step;
            proof {
                assert((step as int) == (old_step as int) + 1);
                assert((sum as int) == (old_sum as int) + (step as int));
                assert((old_sum as int) == Self::tri(old_step as int));
                assert(Self::tri(step as int) == Self::tri(old_step as int) + step as int) by (nonlinear_arith)
                    requires
                        (step as int) == (old_step as int) + 1,
                        0 <= (old_step as int),
                ;
                assert((sum as int) == Self::tri(step as int));
                assert forall|m: int| 0 <= m < (step as int) implies #[trigger] Self::tri(m) < (target_abs as int) by {
                    if m < (old_step as int) {
                        assert(Self::tri(m) < (target_abs as int));
                    } else {
                        assert(m == (old_step as int));
                        assert(Self::tri(m) == (old_sum as int));
                        assert((old_sum as int) < (target_abs as int));
                    }
                };
            }
        }

        let ghost need_adjust = ((sum as int) - (target_abs as int)) % 2 != 0;
        if (sum - target_abs) % 2 != 0 {
            proof {
                assert(!Self::valid_steps(target_abs as int, step as int));
                assert((Self::tri(step as int) - (target_abs as int)) % 2 != 0);
                assert((sum as int) + ((step as int) + 1) < (i32::MAX as int)) by (nonlinear_arith)
                    requires
                        (step as int) <= 50_000,
                        (sum as int) == Self::tri(step as int),
                ;
            }
            let old_step = step;
            let old_sum = sum;
            step += 1;
            sum += step;
            proof {
                assert((step as int) == (old_step as int) + 1);
                assert((sum as int) == (old_sum as int) + (step as int));
                assert((old_sum as int) == Self::tri(old_step as int));
                assert(Self::tri(step as int) == Self::tri(old_step as int) + step as int) by (nonlinear_arith)
                    requires
                        (step as int) == (old_step as int) + 1,
                        0 <= (old_step as int),
                ;
                assert((sum as int) == Self::tri(step as int));
                assert((step as int) <= 50_001);
                assert forall|m: int| 0 <= m < (step as int) implies !#[trigger] Self::valid_steps(target_abs as int, m) by {
                    if m < (old_step as int) {
                        assert(Self::tri(m) < (target_abs as int));
                    } else {
                        assert(m == (old_step as int));
                        assert((Self::tri(m) - (target_abs as int)) % 2 != 0);
                    }
                };
            }

            if (sum - target_abs) % 2 != 0 {
                proof {
                    assert((Self::tri(step as int) - (target_abs as int)) % 2 != 0);
                    if step % 2 != 0 {
                        assert(((sum as int) - (target_abs as int)) % 2 == 0) by (nonlinear_arith)
                            requires
                                ((old_sum as int) - (target_abs as int)) % 2 != 0,
                                (sum as int) == (old_sum as int) + (step as int),
                                (step as int) % 2 != 0,
                        ;
                    }
                    assert(step % 2 == 0);
                    assert((sum as int) + ((step as int) + 1) < (i32::MAX as int)) by (nonlinear_arith)
                        requires
                            (step as int) <= 50_001,
                            (sum as int) == Self::tri(step as int),
                    ;
                }
                let old_step = step;
                let old_sum = sum;
                step += 1;
                sum += step;
                proof {
                    assert((step as int) == (old_step as int) + 1);
                    assert((sum as int) == (old_sum as int) + (step as int));
                    assert((old_sum as int) == Self::tri(old_step as int));
                    assert(Self::tri(step as int) == Self::tri(old_step as int) + step as int) by (nonlinear_arith)
                        requires
                            (step as int) == (old_step as int) + 1,
                            0 <= (old_step as int),
                    ;
                    assert((sum as int) == Self::tri(step as int));
                    assert((step as int) <= 50_002);
                    assert forall|m: int| 0 <= m < (step as int) implies !#[trigger] Self::valid_steps(target_abs as int, m) by {
                        if m < (old_step as int) {
                            assert(!Self::valid_steps(target_abs as int, m));
                        } else {
                            assert(m == (old_step as int));
                            assert((Self::tri(m) - (target_abs as int)) % 2 != 0);
                        }
                    };
                    assert(((sum as int) - (target_abs as int)) % 2 == 0) by (nonlinear_arith)
                        requires
                            ((old_sum as int) - (target_abs as int)) % 2 != 0,
                            (sum as int) == (old_sum as int) + (step as int),
                            (step as int) % 2 != 0,
                    ;
                }
            }
        }

        proof {
            assert(Self::valid_steps(target_abs as int, step as int));
            assert((step as int) <= 50_002);
            assert forall|m: int| 0 <= m < (step as int) implies !#[trigger] Self::valid_steps(target_abs as int, m) by {
                if need_adjust {
                    assert(!Self::valid_steps(target_abs as int, m));
                } else {
                    assert(Self::tri(m) < (target_abs as int));
                }
            };
        }
        step
    }
}

}
