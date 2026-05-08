use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn feasible_team_count(n: int, m: int, t: int) -> bool {
    0 <= t <= n && 0 <= t <= m && t <= (n + m) / 3
}

impl Solution {
    pub fn max_training_teams(n: i64, m: i64) -> (result: i64)
        requires
            0 <= n <= 500000,
            0 <= m <= 500000,
        ensures
            feasible_team_count(n as int, m as int, result as int),
            forall|t: int| feasible_team_count(n as int, m as int, t) ==> t <= result as int,
    {
        let mut ans = if n < m { n } else { m };
        let by_total = (n + m) / 3;
        if by_total < ans {
            ans = by_total;
        }
        ans
    }
}

}
