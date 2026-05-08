use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_team(team: Seq<int>, scores: Seq<i32>, ages: Seq<i32>) -> bool {
    &&& forall|k: int| 0 <= k < team.len() ==> 0 <= #[trigger] team[k] < scores.len() as int
    &&& forall|k: int, l: int| 0 <= k < l < team.len() ==> team[k] != team[l]
    &&& forall|k: int, l: int| 0 <= k < team.len() && 0 <= l < team.len()
        ==> (ages[team[k]] < ages[team[l]] ==> scores[team[k]] <= scores[team[l]])
}

pub open spec fn team_score_sum(team: Seq<int>, scores: Seq<i32>) -> int
    decreases team.len(),
{
    if team.len() <= 0 {
        0
    } else {
        scores[team.last()] as int + team_score_sum(team.drop_last(), scores)
    }
}

impl Solution {
    pub fn best_team_score(scores: Vec<i32>, ages: Vec<i32>) -> (res: i32)
        requires
            1 <= scores.len() <= 1000,
            scores.len() == ages.len(),
            forall|i: int| 0 <= i < scores.len() ==> 1 <= #[trigger] scores[i] <= 1_000_000,
            forall|i: int| 0 <= i < ages.len() ==> 1 <= #[trigger] ages[i] <= 1000,
        ensures
            res >= 1,
            exists|team: Seq<int>| is_valid_team(team, scores@, ages@)
                && team_score_sum(team, scores@) == res as int,
            forall|team: Seq<int>| is_valid_team(team, scores@, ages@)
                ==> team_score_sum(team, scores@) <= res as int,
    {
    }
}

}
