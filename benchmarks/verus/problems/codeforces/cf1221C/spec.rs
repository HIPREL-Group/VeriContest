use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn feasible_teams(c: int, m: int, x: int, t: int) -> bool {
    0 <= t && t <= c && t <= m && 3 * t <= c + m + x
}

impl Solution {
    pub fn max_perfect_teams(c: i64, m: i64, x: i64) -> (res: i64)
        requires
            0 <= c <= 100_000_000,
            0 <= m <= 100_000_000,
            0 <= x <= 100_000_000,
        ensures
            feasible_teams(c as int, m as int, x as int, res as int),
            forall|t: int|
                #[trigger] feasible_teams(c as int, m as int, x as int, t) ==> t <= res as int,
    {
    }
}

}
