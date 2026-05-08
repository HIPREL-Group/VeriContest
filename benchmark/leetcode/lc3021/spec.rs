use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub open spec fn alice_wins(x: int, y: int) -> bool {
        (x + y) % 2 == 1
    }

    pub fn flower_game(n: i32, m: i32) -> (result: i64)
        requires
            1 <= n <= 100000,
            1 <= m <= 100000,
        ensures
            result == (((n as u128) * (m as u128)) / 2) as i64,
            forall |x: int, y: int| 1 <= x <= n && 1 <= y <= m ==> (#[trigger] Self::alice_wins(x, y) <==> (x % 2 != y % 2)),
    {
    }
}
}
