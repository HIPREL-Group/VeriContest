use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_first_contributing_year(n: int, k: int) -> int {
    n - k + 1
}

pub open spec fn spec_odd_integers_in_interval(L: int, n: int) -> int {
    (n + 1) / 2 - L / 2
}

pub open spec fn spec_major_oak_leaves_even(n: int, k: int) -> bool {
    (spec_odd_integers_in_interval(n - k + 1, n) % 2) == 0
}

impl Solution {
    pub fn major_oak_leaves_even(n: i64, k: i64) -> (r: bool)
        requires
            1 <= n <= 1_000_000_000,
            1 <= k <= n,
        ensures
            r == spec_major_oak_leaves_even(n as int, k as int),
    {
    }
}

}
