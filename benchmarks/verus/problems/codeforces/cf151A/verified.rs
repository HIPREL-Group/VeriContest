use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min3(a: int, b: int, c: int) -> int {
    let ab = if a < b { a } else { b };
    if ab < c { ab } else { c }
}

impl Solution {
    pub fn max_toasts(n: u64, k: u64, l: u64, c: u64, d: u64, p: u64, nl: u64, np: u64) -> (result: u64)
        requires
            1 <= n <= 1000,
            1 <= k <= 1000,
            1 <= l <= 1000,
            1 <= c <= 1000,
            1 <= d <= 1000,
            1 <= p <= 1000,
            1 <= nl <= 1000,
            1 <= np <= 1000,
        ensures
            result as int == min3((k * l) as int / nl as int, (c * d) as int, p as int / np as int) / n as int,
    {
        assert(k * l <= 1_000_000) by(nonlinear_arith) requires 1 <= k <= 1000, 1 <= l <= 1000;
        assert(c * d <= 1_000_000) by(nonlinear_arith) requires 1 <= c <= 1000, 1 <= d <= 1000;
        let drink_toasts = (k * l) / nl;
        let lime_toasts = c * d;
        let salt_toasts = p / np;
        let m1 = if drink_toasts < lime_toasts { drink_toasts } else { lime_toasts };
        let m2 = if m1 < salt_toasts { m1 } else { salt_toasts };
        m2 / n
    }
}

}
