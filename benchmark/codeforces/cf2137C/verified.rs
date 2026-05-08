use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_choice(k: int, b: int) -> bool {
    1 <= k && b % k == 0
}

pub open spec fn transformed_sum(a: int, b: int, k: int) -> int {
    a * k + b / k
}

impl Solution {
    pub fn maximum_even_sum(a: i128, b: i128) -> (res: i128)
        requires
            a >= 1,
            b >= 1,
            a <= 1000000000000000000,
            b <= 1000000000000000000,
            (a as int) * (b as int) <= 1000000000000000000,
        ensures
            res == -1 || (res >= 2 && res % 2 == 0),
            res != -1 ==> exists|k: int|
                #[trigger] valid_choice(k, b as int)
                && transformed_sum(a as int, b as int, k) == res,
            res != -1 ==> forall|k: int|
                valid_choice(k, b as int)
                && #[trigger] transformed_sum(a as int, b as int, k) % 2 == 0
                ==> transformed_sum(a as int, b as int, k) <= res,
            res == -1 ==> forall|k: int|
                #[trigger] valid_choice(k, b as int)
                ==> transformed_sum(a as int, b as int, k) % 2 != 0,
    {
        let mut k: i128 = 1;
        let mut found: bool = false;
        let mut best: i128 = -1;
        let mut best_k: i128 = 1;

        while k <= b
            invariant
                1 <= a,
                1 <= b,
                a <= 1000000000000000000,
                b <= 1000000000000000000,
                (a as int) * (b as int) <= 1_000_000_000_000_000_000,
                1 <= k <= b + 1,
                found ==> 1 <= best_k < k,
                found ==> valid_choice(best_k as int, b as int),
                found ==> transformed_sum(a as int, b as int, best_k as int) == best as int,
                found ==> best % 2 == 0,
                found ==> forall|t: int|
                    1 <= t < k as int
                    && valid_choice(t, b as int)
                    && #[trigger] transformed_sum(a as int, b as int, t) % 2 == 0
                    ==> transformed_sum(a as int, b as int, t) <= best as int,
                !found ==> best == -1,
                !found ==> forall|t: int|
                    1 <= t < k as int
                    && #[trigger] valid_choice(t, b as int)
                    ==> transformed_sum(a as int, b as int, t) % 2 != 0,
            decreases b - k + 1,
        {
            let cur_k = k;
            let prev_found = found;
            let prev_best = best;
            let mut cur_valid = false;
            let mut cur_even = false;
            let mut cur_sum: i128 = 0;

            if b % cur_k == 0 {
                cur_valid = true;
                proof {
                    assert((a as int) * (cur_k as int) <= (a as int) * (b as int)) by (nonlinear_arith)
                        requires
                            a as int >= 1,
                            cur_k as int <= b as int,
                    ;
                    assert((a as int) * (cur_k as int) <= 1_000_000_000_000_000_000);
                    assert(1 <= cur_k as int);
                }
                let prod = a * cur_k;
                proof {
                    assert(prod as int == (a as int) * (cur_k as int));
                    assert(prod <= 1_000_000_000_000_000_000);
                    assert((b / cur_k) <= 1_000_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            b <= 1000000000000000000,
                            1 <= cur_k,
                    ;
                    assert(prod + b / cur_k <= 2_000_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            prod <= 1_000_000_000_000_000_000,
                            b / cur_k <= 1_000_000_000_000_000_000,
                    ;
                }
                cur_sum = prod + b / cur_k;
                cur_even = cur_sum % 2 == 0;

                if cur_even {
                    if !found || cur_sum > best {
                        proof {
                            assert(cur_sum % 2 == 0);
                        }
                        best = cur_sum;
                        best_k = cur_k;
                        found = true;
                    }
                }
            }

            proof {
                assert(cur_k as int == k as int);
                assert(1 <= cur_k as int <= b as int);
                if cur_valid {
                    assert(valid_choice(cur_k as int, b as int));
                    assert((b as int) % (cur_k as int) == 0);
                    assert(transformed_sum(a as int, b as int, cur_k as int) == cur_sum as int);
                    if cur_even {
                        assert(cur_sum % 2 == 0);
                        if found {
                            assert(best >= cur_sum);
                        }
                    } else {
                        assert(cur_sum % 2 != 0);
                    }
                }

                if found {
                    assert forall|t: int|
                        1 <= t < (k as int + 1)
                        && valid_choice(t, b as int)
                        && #[trigger] transformed_sum(a as int, b as int, t) % 2 == 0
                        implies transformed_sum(a as int, b as int, t) <= best as int by {
                        if t < k as int {
                            if prev_found {
                                assert(transformed_sum(a as int, b as int, t) <= prev_best as int);
                                assert(prev_best as int <= best as int);
                            } else {
                                assert(transformed_sum(a as int, b as int, t) % 2 != 0);
                            }
                        } else {
                            assert(t == k as int);
                            assert(cur_valid);
                            assert(cur_even);
                            assert(transformed_sum(a as int, b as int, t) == cur_sum as int);
                            assert(cur_sum as int <= best as int);
                        }
                    };
                }

                if !found {
                    assert forall|t: int|
                        1 <= t < (k as int + 1)
                        && #[trigger] valid_choice(t, b as int)
                        implies transformed_sum(a as int, b as int, t) % 2 != 0 by {
                        if t < k as int {
                            assert(transformed_sum(a as int, b as int, t) % 2 != 0);
                        } else {
                            assert(t == k as int);
                            if cur_valid {
                                assert(!cur_even);
                                assert(transformed_sum(a as int, b as int, t) == cur_sum as int);
                                assert(transformed_sum(a as int, b as int, t) % 2 != 0);
                            }
                        }
                    };
                    assert(best == -1);
                }
            }

            proof {
                assert(k <= b);
                assert(b <= 1000000000000000000);
                assert(k + 1 <= 1_000_000_000_000_000_001);
            }
            k = k + 1;
        }

        if found {
            proof {
                assert(1 <= best_k as int <= b as int);
                assert(valid_choice(best_k as int, b as int));
                assert(transformed_sum(a as int, b as int, best_k as int) == best as int);
                assert(best % 2 == 0);
                assert((b as int) / (best_k as int) >= 1) by (nonlinear_arith)
                    requires
                        1 <= best_k as int,
                        best_k as int <= b as int,
                ;
                assert(best as int >= 2) by (nonlinear_arith)
                    requires
                        transformed_sum(a as int, b as int, best_k as int) == best as int,
                        a as int >= 1,
                        best_k as int >= 1,
                        (b as int) / (best_k as int) >= 1,
                ;
                assert forall|t: int|
                    valid_choice(t, b as int)
                    && #[trigger] transformed_sum(a as int, b as int, t) % 2 == 0
                    implies transformed_sum(a as int, b as int, t) <= best as int by {
                    assert(1 <= t);
                    assert(t <= b as int) by (nonlinear_arith)
                        requires
                            b as int % t == 0,
                            1 <= t,
                            b as int >= 1,
                    ;
                    assert(t < k as int);
                };
            }
            best
        } else {
            proof {
                assert(best == -1);
                assert forall|t: int|
                    valid_choice(t, b as int)
                    implies transformed_sum(a as int, b as int, t) % 2 != 0 by {
                    assert(1 <= t);
                    assert(t <= b as int) by (nonlinear_arith)
                        requires
                            b as int % t == 0,
                            1 <= t,
                            b as int >= 1,
                    ;
                    assert(t < k as int);
                };
            }
            -1
        }
    }
}

}