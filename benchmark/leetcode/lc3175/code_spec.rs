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

    pub fn find_winning_player(skills: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= skills.len() <= 100000,
            1 <= k <= 1_000_000_000,
            forall |i: int| 0 <= i < skills.len() ==> 1 <= #[trigger] skills[i] <= 1_000_000,
            forall |i: int, j: int| 0 <= i < j < skills.len() ==> skills[i] != skills[j],
        ensures
            Self::valid_winner_spec(skills@, k as int, result as int),
    {
        let n = skills.len();
        let mut champ = 0usize;
        let mut win = 0i64;
        let mut j = 1usize;
        while j < n {
            if skills[j] > skills[champ] {
                champ = j;
                win = 0;
            }
            win = win.checked_add(1).unwrap_or(win);
            if win == k as i64 {
                break;
            }
            j += 1;
        }
        champ as i32
    }
}

}
