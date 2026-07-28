use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_winner_spec(skills: Seq<i32>, k: int, winner: int) -> bool {
        &&& 2 <= skills.len() <= 100000
        &&& 1 <= k <= 1_000_000_000
        &&& 0 <= winner < skills.len()
        &&& forall |i: int| 0 <= i < skills.len() ==> 1 <= #[trigger] skills[i] <= 1_000_000
        &&& forall |i: int, j: int| 0 <= i < j < skills.len() ==> skills[i] != skills[j]
    }

    pub open spec fn winner_from(skills: Seq<i32>, k: int, i: int, cur: int, win: int) -> int
        decreases skills.len() - i
    {
        if win >= k {
            cur
        } else if i >= skills.len() {
            cur
        } else if skills[i] > skills[cur] {
            Self::winner_from(skills, k, i + 1, i, 1)
        } else {
            Self::winner_from(skills, k, i + 1, cur, win + 1)
        }
    }

    pub open spec fn winner(skills: Seq<i32>, k: int) -> int {
        Self::winner_from(skills, k, 1, 0, 0)
    }

    pub fn find_winning_player(skills: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= skills.len() <= 100000,
            1 <= k <= 1_000_000_000,
            forall |i: int| 0 <= i < skills.len() ==> 1 <= #[trigger] skills[i] <= 1_000_000,
            forall |i: int, j: int| 0 <= i < j < skills.len() ==> skills[i] != skills[j],
        ensures
            Self::valid_winner_spec(skills@, k as int, result as int),
            result as int == Self::winner(skills@, k as int),
    {
    }
}

}
