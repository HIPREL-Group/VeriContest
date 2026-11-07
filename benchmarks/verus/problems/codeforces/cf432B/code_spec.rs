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
        let n = home.len();
        let mut freq = Vec::new();
        let mut z = 0usize;
        while z < 100001 {
            freq.push(0i32);
            z += 1;
        }
        let mut i = 0usize;
        while i < n {
            let cidx = home[i] as usize;
            let oldv = freq[cidx];
            let newv = oldv + 1;
            freq.set(cidx, newv);
            i += 1;
        }
        let mut games_home_kit = Vec::new();
        let mut games_away_kit = Vec::new();
        let mut j = 0usize;
        let nn = n as i32;
        while j < n {
            let aj = away[j];
            let c = aj as usize;
            let cnt = freq[c];
            games_home_kit.push((nn - 1) + cnt);
            games_away_kit.push((nn - 1) - cnt);
            j += 1;
        }
        (games_home_kit, games_away_kit)
    }
}

}
