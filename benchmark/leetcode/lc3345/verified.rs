use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_product(n: int) -> int
        recommends
            1 <= n <= 100,
    {
        if n < 10 {
            n
        } else if n < 100 {
            (n / 10) * (n % 10)
        } else {
            0
        }
    }

    fn digit_product_exec(x: i32) -> (product: i32)
        requires
            1 <= x <= 99,
        ensures
            product as int == Self::digit_product(x as int),
            0 <= product <= 81,
    {
        if x < 10 {
            x
        } else {
            let tens = x / 10;
            let ones = x % 10;
            let mut p: i32 = 0;
            let mut k: i32 = 0;
            while k < ones
                invariant
                    10 <= x <= 99,
                    tens == x / 10,
                    ones == x % 10,
                    1 <= tens <= 9,
                    0 <= ones <= 9,
                    0 <= k <= ones,
                    p as int == k as int * tens as int,
                    0 <= p <= 81,
                decreases ones - k,
            {
                proof {
                    assert(k < ones);
                    assert(k + 1 <= ones);
                    assert((k as int + 1) * tens as int <= ones as int * tens as int) by (nonlinear_arith)
                        requires
                            k + 1 <= ones,
                            tens >= 0,
                    {}
                    assert(ones as int * tens as int <= 81) by (nonlinear_arith)
                        requires
                            0 <= ones <= 9,
                            1 <= tens <= 9,
                    {}
                    assert((k as int + 1) * tens as int <= 81);
                    assert(p as int + tens as int == (k as int + 1) * tens as int) by (nonlinear_arith)
                        requires
                            p as int == k as int * tens as int,
                    {}
                    assert(p + tens <= 81);
                }
                let ghost old_k = k;
                let ghost old_p = p;
                p = p + tens;
                k = k + 1;
                proof {
                    assert(k == old_k + 1);
                    assert(p == old_p + tens);
                    assert(old_p as int == old_k as int * tens as int);
                    assert(p as int == k as int * tens as int) by (nonlinear_arith)
                        requires
                            k == old_k + 1,
                            p == old_p + tens,
                            old_p as int == old_k as int * tens as int,
                    {}
                }
            }
            proof {
                assert(k == ones);
                assert(p as int == ones as int * tens as int);
                assert((x as int) / 10 == tens as int);
                assert((x as int) % 10 == ones as int);
                assert(Self::digit_product(x as int) == (x as int / 10) * (x as int % 10));
            }
            p
        }
    }

    pub fn smallest_number(n: i32, t: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            1 <= t <= 10,
        ensures
            n <= result <= 100,
            Self::digit_product(result as int) % t as int == 0,
            forall|m: int| n as int <= m < result as int ==> #[trigger] (Self::digit_product(m) % t as int) != 0,
    {
        let mut candidate = n;
        while candidate < 100
            invariant
                1 <= n <= 100,
                1 <= t <= 10,
                n <= candidate <= 100,
                forall|m: int| n as int <= m < candidate as int ==> #[trigger] (Self::digit_product(m) % t as int) != 0,
            decreases 100 - candidate,
        {
            let product = Self::digit_product_exec(candidate);
            if product % t == 0 {
                return candidate;
            }
            proof {
                assert(product as int == Self::digit_product(candidate as int));
                assert(Self::digit_product(candidate as int) % t as int != 0);
                assert forall|m: int| n as int <= m < candidate as int + 1 implies #[trigger] (Self::digit_product(m) % t as int) != 0 by {
                    if m < candidate as int {
                    } else {
                        assert(m == candidate as int);
                    }
                }
            }
            candidate += 1;
        }
        proof {
            assert(candidate == 100);
            assert(Self::digit_product(100) == 0);
            assert(1 <= t as int);
            assert((0int) % (t as int) == 0);
            assert(Self::digit_product(100) % t as int == 0);
        }
        100
    }
}

}
