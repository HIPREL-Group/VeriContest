use vstd::prelude::*;

fn main() {}

verus! {

use vstd::arithmetic::mul::lemma_mul_upper_bound;



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
        let m = a * (a + 2);
        let v = m + 2;
        let r = v as i64;
        r
    }
}

}
