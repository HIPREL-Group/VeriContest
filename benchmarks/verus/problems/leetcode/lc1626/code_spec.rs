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
        let n = scores.len();
        let mut scores = scores;
        let mut ages = ages;
        let mut i: usize = 0;
        while i < n {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n {
                if ages[j] < ages[min_idx]
                    || (ages[j] == ages[min_idx] && scores[j] < scores[min_idx])
                {
                    min_idx = j;
                }
                j += 1;
            }
            let tmp_a = ages[i];
            let tmp_s = scores[i];
            ages[i] = ages[min_idx];
            scores[i] = scores[min_idx];
            ages[min_idx] = tmp_a;
            scores[min_idx] = tmp_s;
            i += 1;
        }
        let mut dp: Vec<i64> = Vec::new();
        i = 0;
        while i < n {
            dp.push(scores[i] as i64);
            i += 1;
        }
        i = 1;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                if scores[j] <= scores[i] {
                    if dp[j] + scores[i] as i64 > dp[i] {
                        dp.set(i, dp[j] + scores[i] as i64);
                    }
                }
                j += 1;
            }
            i += 1;
        }
        let mut best: i64 = dp[0];
        let mut k: usize = 1;
        while k < n {
            if dp[k] > best {
                best = dp[k];
            }
            k += 1;
        }
        best as i32
    }
}

}
