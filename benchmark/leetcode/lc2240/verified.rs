use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ways_prefix(total: int, cost1: int, cost2: int, steps: int) -> int
        decreases steps,
    {
        if steps <= 0 {
            0
        } else {
            let pens = steps - 1;
            Self::ways_prefix(total, cost1, cost2, steps - 1)
                + ((total - pens * cost1) / cost2 + 1)
        }
    }

    pub fn ways_to_buy_pens_pencils(total: i32, cost1: i32, cost2: i32) -> (ans: i64)
        requires
            1 <= total <= 1000000,
            1 <= cost1 <= 1000000,
            1 <= cost2 <= 1000000,
        ensures
            ans as int == Self::ways_prefix(total as int, cost1 as int, cost2 as int, (total / cost1 + 1) as int),
    {
        let t = total as i64;
        let c1 = cost1 as i64;
        let c2 = cost2 as i64;
        let max_pens = t / c1;
        let mut pens: i64 = 0;
        let mut ans: i64 = 0;
        while pens <= max_pens
            invariant
                t == total as i64,
                c1 == cost1 as i64,
                c2 == cost2 as i64,
                1 <= t <= 1000000,
                1 <= c1 <= 1000000,
                1 <= c2 <= 1000000,
                0 <= max_pens <= 1000000,
                max_pens == t / c1,
                0 <= pens <= max_pens + 1,
                ans as int == Self::ways_prefix(total as int, cost1 as int, cost2 as int, pens as int),
                0 <= ans <= pens * 1000001,
            decreases max_pens + 1 - pens,
        {
            proof {
                assert(0 <= pens <= max_pens);
                assert(0 <= pens * c1 <= t) by (nonlinear_arith)
                    requires
                        0 <= pens,
                        1 <= c1,
                        pens <= max_pens,
                        max_pens == t / c1;
                assert(0 <= t - pens * c1 <= 1000000) by (nonlinear_arith)
                    requires
                        0 <= pens * c1 <= t,
                        t <= 1000000;
                assert((((t - pens * c1) as int) / (c2 as int)) + 1 <= 1000001) by (nonlinear_arith)
                    requires
                        0 <= t - pens * c1 <= 1000000,
                        1 <= c2;
                assert((ans as int) + ((((t - pens * c1) as int) / (c2 as int)) + 1) <= ((pens + 1) as int) * 1000001) by (nonlinear_arith)
                    requires
                        ans <= pens * 1000001,
                        ((((t - pens * c1) as int) / (c2 as int)) + 1) <= 1000001;
            }
            ans = ans + (t - pens * c1) / c2 + 1;
            pens = pens + 1;
        }
        ans
    }
}

}
