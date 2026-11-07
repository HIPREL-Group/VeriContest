use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn remove_zeros_acc(m: int, place: int, acc: int) -> int
        decreases m,
    {
        if m <= 0 {
            acc
        } else {
            let d = m % 10;
            if d == 0 {
                Self::remove_zeros_acc(m / 10, place, acc)
            } else {
                Self::remove_zeros_acc(m / 10, place * 10, acc + d * place)
            }
        }
    }

    pub open spec fn remove_zeros_spec(n: int) -> int {
        Self::remove_zeros_acc(n, 1, 0)
    }

    pub fn remove_zeros(n: i64) -> (res: i64)
        requires
            1 <= n <= 1_000_000_000_000_000,
        ensures
            res as int == Self::remove_zeros_spec(n as int),
    {
        let mut m: i64 = n;
        let mut place: i64 = 1;
        let mut res: i64 = 0;

        while m > 0
            invariant
                1 <= n <= 1_000_000_000_000_000,
                0 <= m,
                1 <= place,
                0 <= res,
                res as int + m as int * place as int <= n as int * 10,
                Self::remove_zeros_acc(m as int, place as int, res as int) == Self::remove_zeros_spec(
                    n as int,
                ),
            decreases m,
        {
            let ghost old_m: int = m as int;
            let ghost old_place: int = place as int;
            let ghost old_res: int = res as int;

            let digit: i64 = m % 10;

            proof {
                lemma_fundamental_div_mod(old_m, 10);
                assert(old_m == 10 * (old_m / 10) + old_m % 10);
                assert(0 <= old_m % 10 < 10);
                assert(digit as int == old_m % 10);
                assert(0 <= digit <= 9);
            }

            if digit != 0 {
                proof {
                    assert(old_m >= 1);
                    assert(old_m * old_place <= n as int * 10) by (nonlinear_arith)
                        requires
                            old_res + old_m * old_place <= n as int * 10,
                            0 <= old_res,
                    {
                    }
                    assert(old_place <= old_m * old_place) by (nonlinear_arith)
                        requires
                            old_m >= 1,
                            1 <= old_place,
                    {
                    }
                    assert(old_place <= n as int * 10) by (nonlinear_arith)
                        requires
                            old_place <= old_m * old_place,
                            old_m * old_place <= n as int * 10,
                    {
                    }
                    assert(old_res <= n as int * 10) by (nonlinear_arith)
                        requires
                            old_res + old_m * old_place <= n as int * 10,
                            0 <= old_m * old_place,
                    {
                    }
                    assert(n as int * 10 <= 10_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            n <= 1_000_000_000_000_000,
                    {
                    }
                    assert(old_place <= 10_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            old_place <= n as int * 10,
                            n as int * 10 <= 10_000_000_000_000_000,
                    {
                    }
                    assert(old_res <= 10_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            old_res <= n as int * 10,
                            n as int * 10 <= 10_000_000_000_000_000,
                    {
                    }
                    assert(1 <= digit as int <= 9);
                    assert((digit as int) * old_place <= 9 * old_place) by (nonlinear_arith)
                        requires
                            digit as int <= 9,
                            0 <= old_place,
                    {
                    }
                    assert(9 * old_place <= 90_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            old_place <= 10_000_000_000_000_000,
                    {
                    }
                    assert(old_res + (digit as int) * old_place <= 100_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            old_res <= 10_000_000_000_000_000,
                            (digit as int) * old_place <= 90_000_000_000_000_000,
                    {
                    }
                    assert(old_place * 10 <= 100_000_000_000_000_000) by (nonlinear_arith)
                        requires
                            old_place <= 10_000_000_000_000_000,
                    {
                    }
                    assert(0 <= (digit as int) * old_place <= i64::MAX as int) by (nonlinear_arith)
                        requires
                            1 <= digit as int,
                            0 <= old_place,
                            (digit as int) * old_place <= 90_000_000_000_000_000,
                    {
                    }
                    assert(0 <= old_res + (digit as int) * old_place <= i64::MAX as int) by (nonlinear_arith)
                        requires
                            0 <= old_res,
                            0 <= (digit as int) * old_place,
                            old_res + (digit as int) * old_place <= 100_000_000_000_000_000,
                    {
                    }
                    assert(0 <= old_place * 10 <= i64::MAX as int) by (nonlinear_arith)
                        requires
                            1 <= old_place,
                            old_place * 10 <= 100_000_000_000_000_000,
                    {
                    }
                }

                res = res + digit * place;
                place = place * 10;
            }

            m = m / 10;

            proof {
                assert(old_m > 0);
                assert(m as int == old_m / 10);
                assert(digit as int == old_m % 10);

                if digit == 0 {
                    assert(res as int == old_res);
                    assert(place as int == old_place);
                    assert(
                        Self::remove_zeros_acc(old_m, old_place, old_res) == Self::remove_zeros_acc(
                            old_m / 10,
                            old_place,
                            old_res,
                        )
                    );
                    assert((m as int) * (place as int) <= old_m * old_place) by (nonlinear_arith)
                        requires
                            m as int == old_m / 10,
                            place as int == old_place,
                            0 <= old_m,
                            0 <= old_place,
                    {
                    }
                    assert(res as int + m as int * place as int <= n as int * 10) by (nonlinear_arith)
                        requires
                            res as int == old_res,
                            (m as int) * (place as int) <= old_m * old_place,
                            old_res + old_m * old_place <= n as int * 10,
                    {
                    }
                } else {
                    assert(res as int == old_res + (digit as int) * old_place);
                    assert(place as int == old_place * 10);
                    assert(
                        Self::remove_zeros_acc(old_m, old_place, old_res) == Self::remove_zeros_acc(
                            old_m / 10,
                            old_place * 10,
                            old_res + (digit as int) * old_place,
                        )
                    );
                    assert(
                        res as int + m as int * place as int == old_res + old_m * old_place
                    ) by (nonlinear_arith)
                        requires
                            res as int == old_res + (digit as int) * old_place,
                            m as int == old_m / 10,
                            place as int == old_place * 10,
                            old_m == 10 * (old_m / 10) + digit as int,
                    {
                    }
                    assert(res as int + m as int * place as int <= n as int * 10) by (nonlinear_arith)
                        requires
                            res as int + m as int * place as int == old_res + old_m * old_place,
                            old_res + old_m * old_place <= n as int * 10,
                    {
                    }
                }

                assert(
                    Self::remove_zeros_acc(m as int, place as int, res as int) == Self::remove_zeros_spec(
                        n as int,
                    )
                ) by {
                    assert(
                        Self::remove_zeros_acc(m as int, place as int, res as int) == Self::remove_zeros_acc(
                            old_m,
                            old_place,
                            old_res,
                        )
                    );
                }
            }
        }

        proof {
            assert(m == 0);
            assert(Self::remove_zeros_acc(0, place as int, res as int) == res as int);
            assert(Self::remove_zeros_acc(m as int, place as int, res as int) == Self::remove_zeros_spec(n as int));
        }

        res
    }
}

}
