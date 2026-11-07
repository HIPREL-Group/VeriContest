use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_odds_up_to(n: int) -> int {
    (n + 1) / 2
}

impl Solution {
    pub fn count_odds(low: i32, high: i32) -> (res: i32)
        requires
            0 <= low <= high <= 1_000_000_000,
        ensures
            0 <= res,
            res == count_odds_up_to(high as int) - count_odds_up_to(low as int - 1),
    {
        (high + 1) / 2 - low / 2
    }
}

}
