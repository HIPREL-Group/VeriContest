use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_odds_spec(n: int) -> int {
    (n + 1) / 2
}

pub open spec fn value_at_position(n: int, k: int) -> int
    recommends
        1 <= k <= n,
{
    if k <= count_odds_spec(n) {
        2 * k - 1
    } else {
        2 * (k - count_odds_spec(n))
    }
}

impl Solution {
    pub fn kth_even_odds(n: u64, k: u64) -> (result: u64)
        requires
            1 <= k <= n,
            n <= 1_000_000_000_000,
        ensures
            result as int == value_at_position(n as int, k as int),
        {
    }
}

}
