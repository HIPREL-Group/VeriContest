use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn apples(r: int) -> int {
    2 * r * (r + 1) * (2 * r + 1)
}

proof fn lemma_apples_monotonic(r1: int, r2: int)
    requires
        0 < r1 <= r2,
    ensures
        apples(r1) <= apples(r2),
{
    assert(2 * r1 * (r1 + 1) * (2 * r1 + 1) <= 2 * r2 * (r2 + 1) * (2 * r2 + 1)) by(nonlinear_arith)
        requires 0 < r1 <= r2;
}

impl Solution {
    pub fn minimum_perimeter(needed_apples: i64) -> (result: i64)
        requires
            1 <= needed_apples <= 1_000_000_000_000_000i64,
        ensures
            result >= 8,
            result % 8 == 0,
            apples(result as int / 8) >= needed_apples as int,
            forall |r: int| 0 < r < result as int / 8 ==> apples(r) < needed_apples as int,
    {
        let mut lo: i64 = 1;
        let mut hi: i64 = 100_000;

        proof {
            assert(apples(100_000) >= 1_000_000_000_000_000) by(nonlinear_arith);
        }

        while lo < hi
            invariant
                1 <= lo <= hi <= 100_000i64,
                1 <= needed_apples <= 1_000_000_000_000_000i64,
                apples(hi as int) >= needed_apples as int,
                forall |r: int| 0 < r < lo as int ==> apples(r) < needed_apples as int,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;

            assert(2 * mid * (mid + 1) <= 20_000_200_000i64) by(nonlinear_arith)
                requires 1 <= mid <= 100_000;

            assert(2 * mid * (mid + 1) * (2 * mid + 1) <= 4_000_060_000_200_000i64) by(nonlinear_arith)
                requires 1 <= mid <= 100_000;

            let apples_mid = 2 * mid * (mid + 1) * (2 * mid + 1);

            if apples_mid >= needed_apples {
                hi = mid;
            } else {
                proof {
                    assert forall |r: int| 0 < r < mid as int + 1 implies apples(r) < needed_apples as int by {
                        if r >= lo as int {
                            lemma_apples_monotonic(r, mid as int);
                        }
                    }
                }
                lo = mid + 1;
            }
        }

        lo * 8
    }
}

}
