use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn winner_from(n: int, take: int, alice_turn: bool) -> bool
        recommends
            0 <= n,
            0 <= take,
        decreases take
    {
        if take <= 0 || n < take {
            !alice_turn
        } else {
            Self::winner_from(n - take, take - 1, !alice_turn)
        }
    }

    pub fn can_alice_win(n: i32) -> (result: bool)
        requires
            1 <= n <= 50,
        ensures
            result == Self::winner_from(n as int, 10, true),
    {
    }
}

}
