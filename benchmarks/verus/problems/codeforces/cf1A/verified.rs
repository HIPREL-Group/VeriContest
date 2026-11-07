use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn ceil_div(n: int, a: int) -> int {
    (n + a - 1) / a
}

impl Solution {
    pub fn min_flagstones(n: u64, m: u64, a: u64) -> (result: u64)
        requires
            1 <= n <= 1_000_000_000,
            1 <= m <= 1_000_000_000,
            1 <= a <= 1_000_000_000,
        ensures
            result as int == ceil_div(n as int, a as int) * ceil_div(m as int, a as int),
    {
        let rows = (n + a - 1) / a;
        let cols = (m + a - 1) / a;
        proof {
            assert(rows as int == (n as int + a as int - 1) / (a as int));
            assert(rows as int == ceil_div(n as int, a as int));
            assert(cols as int == (m as int + a as int - 1) / (a as int));
            assert(cols as int == ceil_div(m as int, a as int));
            assert(rows <= 2_000_000_000u64);
            assert(cols <= 2_000_000_000u64);
            assert(rows as int * cols as int <= 4_000_000_000_000_000_000) by (nonlinear_arith)
                requires
                    rows as int <= 2_000_000_000,
                    cols as int <= 2_000_000_000,
            {}
            assert(4_000_000_000_000_000_000 < 18446744073709551616) by (nonlinear_arith) {}
        }
        rows * cols
    }
}

}
