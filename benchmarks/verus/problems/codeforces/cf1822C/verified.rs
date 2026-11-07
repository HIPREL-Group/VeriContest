use vstd::prelude::*;

fn main() {}

verus! {

use vstd::arithmetic::mul::lemma_mul_upper_bound;

proof fn lemma_u128_bun_product_fits(n: i64)
    requires
        4 <= n <= 1_000_000_000,
    ensures
        (n as u128) * ((n as u128) + 2) < 340282366920938463463374607431768211456,
        (n as u128) * ((n as u128) + 2) + 2 < 340282366920938463463374607431768211456,
{
    let ni = n as int;
    assert(0 <= ni <= 1_000_000_000);
    let y = ni + 2;
    assert(0 <= y <= 1_000_000_002);
    lemma_mul_upper_bound(ni, 1_000_000_000, y, 1_000_000_002);
    assert(ni * y <= 1_000_000_000 * 1_000_000_002);
    assert(ni * y + 2 <= 1_000_000_000 * 1_000_000_002 + 2);
    assert(1_000_000_000 * 1_000_000_002 + 2 < 340282366920938463463374607431768211456) by (nonlinear_arith);
    assert((n as u128) * ((n as u128) + 2) == (ni * y) as u128);
    assert((n as u128) * ((n as u128) + 2) + 2 == (ni * y + 2) as u128);
}

proof fn lemma_bun_fits_i64(n: i64)
    requires
        4 <= n <= 1_000_000_000,
    ensures
        (n as int) * ((n as int) + 2) + 2 < 9223372036854775807,
{
    let ni = n as int;
    let y = ni + 2;
    assert(0 <= ni <= 1_000_000_000);
    assert(0 <= y <= 1_000_000_002);
    lemma_mul_upper_bound(ni, 1_000_000_000, y, 1_000_000_002);
    assert(ni * y + 2 <= 1_000_000_000 * 1_000_000_002 + 2);
    assert(1_000_000_000 * 1_000_000_002 + 2 < 9223372036854775807) by (nonlinear_arith);
}

pub struct Solution;

pub open spec fn spec_bun_chocolate_total(n: int) -> int {
    n * (n + 2) + 2
}

impl Solution {
    pub fn bun_chocolate_total(n: i64) -> (r: i64)
        requires
            4 <= n <= 1_000_000_000,
        ensures
            r == spec_bun_chocolate_total(n as int),
    {
        let a = n as u128;
        proof {
            lemma_u128_bun_product_fits(n);
            lemma_bun_fits_i64(n);
            assert((a as int) == (n as int));
            assert((a * (a + 2) + 2) as int == (n as int) * ((n as int) + 2) + 2) by {
                assert((a + 2) as int == (n as int) + 2);
            };
            assert((n as int) * ((n as int) + 2) + 2 == spec_bun_chocolate_total(n as int));
        }
        let m = a * (a + 2);
        let v = m + 2;
        let r = v as i64;
        proof {
            assert forall|k: int|
                #![trigger spec_bun_chocolate_total(k)]
                k == n as int implies r == spec_bun_chocolate_total(k)
            by {
                assert(k == n as int);
                assert(r == spec_bun_chocolate_total(n as int));
            };
            assert(r as int == spec_bun_chocolate_total(n as int));
        }
        r
    }
}

}
