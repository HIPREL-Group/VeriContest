use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_celex_distinct_sums(x1: int, y1: int, x2: int, y2: int) -> int {
    (x2 - x1) * (y2 - y1) + 1
}

impl Solution {
    pub fn celex_distinct_sums(x1: i64, y1: i64, x2: i64, y2: i64) -> (r: i64)
        requires
            1 <= x1 <= x2 <= 1_000_000_000,
            1 <= y1 <= y2 <= 1_000_000_000,
        ensures
            r as int == spec_celex_distinct_sums(x1 as int, y1 as int, x2 as int, y2 as int),
    {
        let dx = x2 - x1;
        let dy = y2 - y1;
        proof {
            assert(dx as int == x2 as int - x1 as int);
            assert(dy as int == y2 as int - y1 as int);
            assert(0 <= dx <= 999_999_999);
            assert(0 <= dy <= 999_999_999);
            assert((dx as int) * (dy as int) <= 999_999_999 * 999_999_999) by (nonlinear_arith)
                requires
                    0 <= dx <= 999_999_999,
                    0 <= dy <= 999_999_999;
            assert(999_999_999 * 999_999_999 < 1_000_000_000_000_000_000) by (nonlinear_arith);
            assert((dx * dy + 1) as int == (dx as int) * (dy as int) + 1);
            assert((dx as int) * (dy as int) + 1 == spec_celex_distinct_sums(
                x1 as int,
                y1 as int,
                x2 as int,
                y2 as int,
            ));
        }
        dx * dy + 1
    }
}

}
