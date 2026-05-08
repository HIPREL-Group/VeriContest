use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn concat_non_zero_acc(m: int, place: int, acc: int) -> int
        decreases m,
    {
        if m <= 0 {
            acc
        } else {
            let d = m % 10;
            if d == 0 {
                Self::concat_non_zero_acc(m / 10, place, acc)
            } else {
                Self::concat_non_zero_acc(m / 10, place * 10, acc + d * place)
            }
        }
    }

    pub open spec fn sum_non_zero_acc(m: int, acc: int) -> int
        decreases m,
    {
        if m <= 0 {
            acc
        } else {
            let d = m % 10;
            if d == 0 {
                Self::sum_non_zero_acc(m / 10, acc)
            } else {
                Self::sum_non_zero_acc(m / 10, acc + d)
            }
        }
    }

    pub open spec fn concat_non_zero(n: int) -> int {
        Self::concat_non_zero_acc(n, 1, 0)
    }

    pub open spec fn sum_non_zero(n: int) -> int {
        Self::sum_non_zero_acc(n, 0)
    }

    pub fn sum_and_multiply(n: i32) -> (res: i64)
        requires
            0 <= n <= 1_000_000_000,
        ensures
            res as int == Self::concat_non_zero(n as int) * Self::sum_non_zero(n as int),
    {
        let mut m: i64 = n as i64;
        let mut place: i64 = 1;
        let mut x: i64 = 0;
        let mut sum: i64 = 0;

        while m > 0
            invariant
                0 <= n <= 1_000_000_000,
                0 <= m,
                1 <= place,
                0 <= x,
                0 <= sum,
                sum as int <= x as int,
                x as int + m as int * place as int <= n as int,
                Self::concat_non_zero_acc(m as int, place as int, x as int) == Self::concat_non_zero(
                    n as int,
                ),
                Self::sum_non_zero_acc(m as int, sum as int) == Self::sum_non_zero(n as int),
            decreases m,
        {
            let ghost old_m: int = m as int;
            let ghost old_place: int = place as int;
            let ghost old_x: int = x as int;
            let ghost old_sum: int = sum as int;

            let digit: i64 = m % 10;

            proof {
                lemma_fundamental_div_mod(old_m, 10);
                assert(old_m == 10 * (old_m / 10) + old_m % 10);
                assert(0 <= old_m % 10 < 10);
                assert(digit as int == old_m % 10);
                assert(0 <= digit <= 9);
                assert(old_m >= 1);
            }

            if digit != 0 {
                proof {
                    assert(old_place <= old_m * old_place) by (nonlinear_arith)
                        requires
                            old_m >= 1,
                            1 <= old_place,
                    {
                    }
                    assert(old_place <= n as int) by (nonlinear_arith)
                        requires
                            old_place <= old_m * old_place,
                            old_x + old_m * old_place <= n as int,
                            0 <= old_x,
                    {
                    }
                    assert(0 <= old_x <= n as int) by (nonlinear_arith)
                        requires
                            0 <= old_x,
                            old_x + old_m * old_place <= n as int,
                            0 <= old_m * old_place,
                    {
                    }
                    assert(0 <= old_sum <= old_x);
                    assert(0 <= old_sum + digit as int <= n as int + 9) by (nonlinear_arith)
                        requires
                            0 <= old_sum <= old_x,
                            0 <= old_x <= n as int,
                            0 <= digit as int <= 9,
                    {
                    }
                    assert(0 <= old_x + (digit as int) * old_place <= 10_000_000_000) by (nonlinear_arith)
                        requires
                            0 <= old_x <= n as int,
                            0 <= digit as int <= 9,
                            0 <= old_place <= n as int,
                            n as int <= 1_000_000_000,
                    {
                    }
                    assert(0 <= old_place * 10 <= 10_000_000_000) by (nonlinear_arith)
                        requires
                            0 <= old_place <= n as int,
                            n as int <= 1_000_000_000,
                    {
                    }
                    assert(0 <= old_sum + digit as int <= i64::MAX as int) by (nonlinear_arith)
                        requires
                            0 <= old_sum + digit as int <= n as int + 9,
                            n as int <= 1_000_000_000,
                    {
                    }
                    assert(0 <= old_x + (digit as int) * old_place <= i64::MAX as int) by (nonlinear_arith)
                        requires
                            0 <= old_x + (digit as int) * old_place <= 10_000_000_000,
                    {
                    }
                    assert(0 <= old_place * 10 <= i64::MAX as int) by (nonlinear_arith)
                        requires
                            0 <= old_place * 10 <= 10_000_000_000,
                    {
                    }
                }

                x = x + digit * place;
                place = place * 10;
                sum = sum + digit;
            }

            m = m / 10;

            proof {
                assert(m as int == old_m / 10);
                assert(digit as int == old_m % 10);

                if digit == 0 {
                    assert(x as int == old_x);
                    assert(place as int == old_place);
                    assert(sum as int == old_sum);

                    assert(
                        Self::concat_non_zero_acc(old_m, old_place, old_x)
                            == Self::concat_non_zero_acc(old_m / 10, old_place, old_x)
                    );
                    assert(
                        Self::sum_non_zero_acc(old_m, old_sum)
                            == Self::sum_non_zero_acc(old_m / 10, old_sum)
                    );

                    assert(m as int * place as int <= old_m * old_place) by (nonlinear_arith)
                        requires
                            m as int == old_m / 10,
                            place as int == old_place,
                            0 <= old_m,
                            0 <= old_place,
                    {
                    }
                    assert(x as int + m as int * place as int <= n as int) by (nonlinear_arith)
                        requires
                            x as int == old_x,
                            m as int * place as int <= old_m * old_place,
                            old_x + old_m * old_place <= n as int,
                    {
                    }
                    assert(sum as int <= x as int);
                    assert(1 <= place as int);
                } else {
                    assert(x as int == old_x + (digit as int) * old_place);
                    assert(place as int == old_place * 10);
                    assert(sum as int == old_sum + digit as int);

                    assert(
                        Self::concat_non_zero_acc(old_m, old_place, old_x)
                            == Self::concat_non_zero_acc(
                                old_m / 10,
                                old_place * 10,
                                old_x + (digit as int) * old_place,
                            )
                    );
                    assert(
                        Self::sum_non_zero_acc(old_m, old_sum)
                            == Self::sum_non_zero_acc(old_m / 10, old_sum + digit as int)
                    );

                    assert(
                        x as int + m as int * place as int == old_x + old_m * old_place
                    ) by (nonlinear_arith)
                        requires
                            x as int == old_x + (digit as int) * old_place,
                            m as int == old_m / 10,
                            place as int == old_place * 10,
                            old_m == 10 * (old_m / 10) + digit as int,
                    {
                    }
                    assert(x as int + m as int * place as int <= n as int) by (nonlinear_arith)
                        requires
                            x as int + m as int * place as int == old_x + old_m * old_place,
                            old_x + old_m * old_place <= n as int,
                    {
                    }
                    assert(sum as int <= x as int) by (nonlinear_arith)
                        requires
                            sum as int == old_sum + digit as int,
                            x as int == old_x + (digit as int) * old_place,
                            old_sum <= old_x,
                            1 <= old_place,
                            0 <= digit as int,
                    {
                    }
                    assert(1 <= place as int) by (nonlinear_arith)
                        requires
                            place as int == old_place * 10,
                            1 <= old_place,
                    {
                    }
                }

                assert(
                    Self::concat_non_zero_acc(m as int, place as int, x as int) == Self::concat_non_zero(
                        n as int,
                    )
                ) by {
                    assert(
                        Self::concat_non_zero_acc(m as int, place as int, x as int)
                            == Self::concat_non_zero_acc(old_m, old_place, old_x)
                    );
                }

                assert(
                    Self::sum_non_zero_acc(m as int, sum as int) == Self::sum_non_zero(n as int)
                ) by {
                    assert(
                        Self::sum_non_zero_acc(m as int, sum as int)
                            == Self::sum_non_zero_acc(old_m, old_sum)
                    );
                }
            }
        }

        proof {
            assert(m == 0);
            assert(Self::concat_non_zero_acc(0, place as int, x as int) == x as int);
            assert(Self::sum_non_zero_acc(0, sum as int) == sum as int);
            assert(Self::concat_non_zero_acc(m as int, place as int, x as int) == Self::concat_non_zero(
                n as int,
            ));
            assert(Self::sum_non_zero_acc(m as int, sum as int) == Self::sum_non_zero(n as int));
            assert(x as int == Self::concat_non_zero(n as int));
            assert(sum as int == Self::sum_non_zero(n as int));
            assert(0 <= x as int <= n as int) by (nonlinear_arith)
                requires
                    x as int + m as int * place as int <= n as int,
                    0 <= x as int,
                    0 <= m as int * place as int,
            {
            }
            assert(0 <= sum as int <= x as int);
            assert(0 <= x as int * sum as int <= 1_000_000_000_000_000_000) by (nonlinear_arith)
                requires
                    0 <= x as int <= n as int,
                    0 <= sum as int <= x as int,
                    n as int <= 1_000_000_000,
            {
            }
            assert(0 <= x as int * sum as int <= i64::MAX as int) by (nonlinear_arith)
                requires
                    0 <= x as int * sum as int <= 1_000_000_000_000_000_000,
            {
            }
        }

        x * sum
    }
}

} 
