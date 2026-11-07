use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    pub open spec fn digit_product(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else {
            (n % 10) * Self::digit_product(n / 10)
        }
    }

    pub open spec fn check_divisibility_spec(n: nat) -> bool {
        let d = Self::digit_sum(n) + Self::digit_product(n);
        d > 0 && n % d == 0
    }

    fn digit_sum_exec(x: u32) -> (sum: u32)
        requires
            x <= 1_000_000,
        ensures
            sum as nat == Self::digit_sum(x as nat),
            sum <= x,
            x > 0 ==> sum > 0,
        decreases x,
    {
        if x == 0 {
            0
        } else {
            let d = x % 10;
            let q = x / 10;
            let s = Self::digit_sum_exec(q);
            if q == 0 {
                assert(x < 10);
                assert(d == x);
                d
            } else {
                proof {
                    assert(x as nat == 10 * q as nat + d as nat);
                    assert(d <= 9);
                    assert(s <= q);
                    assert(d as nat + s as nat <= x as nat) by(nonlinear_arith)
                        requires
                            s as nat <= q as nat,
                            x as nat == 10 * q as nat + d as nat,
                            d <= 9,
                    {}
                }
                d + s
            }
        }
    }

    fn digit_product_exec(x: u32) -> (prod: u32)
        requires
            x <= 1_000_000,
        ensures
            prod as nat == Self::digit_product(x as nat),
            x == 0 ==> prod == 1,
            x > 0 ==> prod <= x,
        decreases x,
    {
        if x == 0 {
            assert(Self::digit_product(x as nat) == 1);
            1
        } else {
            let d = x % 10;
            let q = x / 10;
            let p = Self::digit_product_exec(q);
            if q == 0 {
                assert(x < 10);
                assert(d == x);
                proof {
                    assert(Self::digit_product(x as nat) == (x as nat % 10) * Self::digit_product((x as nat) / 10));
                    assert((x as nat) / 10 == 0);
                    assert(Self::digit_product(0nat) == 1);
                    assert(x as nat % 10 == x as nat);
                }
                d
            } else {
                proof {
                    assert(q > 0);
                    assert(p <= q);
                    assert(d <= 9);
                    assert(x as nat == 10 * q as nat + d as nat);
                    assert(Self::digit_product(x as nat) == d as nat * Self::digit_product(q as nat));
                    assert(p as nat == Self::digit_product(q as nat));
                    assert(d as nat * p as nat <= x as nat) by(nonlinear_arith)
                        requires
                            p as nat <= q as nat,
                            x as nat == 10 * q as nat + d as nat,
                            d <= 9,
                    {}
                }
                d * p
            }
        }
    }

    pub fn check_divisibility(n: i32) -> (result: bool)
        requires
            1 <= n <= 1_000_000,
        ensures
            result == Self::check_divisibility_spec(n as nat),
    {
        let x = n as u32;
        let s = Self::digit_sum_exec(x);
        let p = Self::digit_product_exec(x);
        proof {
            assert(x > 0);
            assert(p <= x);
            assert(s <= x);
            assert(s as nat + p as nat <= 2_000_000) by(nonlinear_arith)
                requires
                    s as nat <= x as nat,
                    p as nat <= x as nat,
                    x as nat <= 1_000_000,
            {}
        }
        let denom = s + p;
        assert(denom > 0);
        x % denom == 0
    }
}

}
