use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_home_prefix(home: Seq<i32>, k: int, color: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        count_home_prefix(home, k - 1, color) + if home[k - 1] == color { 1int } else { 0int }
    }
}

impl Solution {
    pub fn football_kit_games(home: Vec<i32>, away: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
        requires
            2 <= home.len() <= 100_000,
            home.len() == away.len(),
            forall|i: int| 0 <= i < home.len() ==> 1 <= #[trigger] home[i] && home[i] <= 100_000,
            forall|i: int| 0 <= i < away.len() ==> 1 <= #[trigger] away[i] && away[i] <= 100_000,
            forall|i: int| 0 <= i < home.len() ==> #[trigger] home[i] != away[i],
        ensures
            result.0.len() == home.len(),
            result.1.len() == home.len(),
            forall|i: int| 0 <= i < home.len() ==> result.0[i] as int == (home.len() as int - 1)
                + count_home_prefix(home@, home.len() as int, away[i] as int)
                && result.1[i] as int == (home.len() as int - 1)
                    - count_home_prefix(home@, home.len() as int, away[i] as int),
    {
    }
}

}
