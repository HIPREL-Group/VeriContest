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
    }
}

}
