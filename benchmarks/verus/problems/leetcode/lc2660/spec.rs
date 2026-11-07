use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn turn_value(scores: Seq<i32>, i: int) -> int
        recommends
            0 <= i < scores.len(),
    {
        if (i >= 1 && scores[i - 1] == 10) || (i >= 2 && scores[i - 2] == 10) {
            2 * scores[i] as int
        } else {
            scores[i] as int
        }
    }

    pub open spec fn prefix_score(scores: Seq<i32>, upto: nat) -> int
        recommends
            upto <= scores.len(),
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::prefix_score(scores, (upto - 1) as nat)
                + Self::turn_value(scores, (upto - 1) as int)
        }
    }

    pub open spec fn winner_spec(player1: Seq<i32>, player2: Seq<i32>) -> int
        recommends
            player1.len() == player2.len(),
    {
        let s1 = Self::prefix_score(player1, player1.len() as nat);
        let s2 = Self::prefix_score(player2, player2.len() as nat);
        if s1 > s2 {
            1
        } else if s2 > s1 {
            2
        } else {
            0
        }
    }

    pub fn is_winner(player1: Vec<i32>, player2: Vec<i32>) -> (result: i32)
        requires
            player1.len() == player2.len(),
            1 <= player1.len() <= 1000,
            forall |i: int| 0 <= i < player1.len() ==> 0 <= #[trigger] player1[i] <= 10,
            forall |i: int| 0 <= i < player2.len() ==> 0 <= #[trigger] player2[i] <= 10,
        ensures
            result as int == Self::winner_spec(player1@, player2@),
    {
    }
}

}
