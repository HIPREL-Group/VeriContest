use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_host_guest_match(home: Seq<i32>, away: Seq<i32>, i: int, j: int) -> bool
    recommends 0 <= i < home.len(), 0 <= j < away.len(),
{
    i != j && home[i] == away[j]
}

pub open spec fn count_matches_at_i(home: Seq<i32>, away: Seq<i32>, i: int, j_end: int) -> nat
    recommends
        0 <= i < home.len(),
        0 <= j_end <= away.len(),
    decreases j_end,
{
    if j_end <= 0 {
        0nat
    } else {
        let j = j_end - 1;
        let inc = if is_host_guest_match(home, away, i, j) { 1nat } else { 0nat };
        count_matches_at_i(home, away, i, j_end - 1) + inc
    }
}

pub open spec fn count_host_guest_pairs(home: Seq<i32>, away: Seq<i32>, n: int, total_n: int) -> nat
    recommends
        0 <= n <= total_n,
        0 <= total_n <= home.len(),
        0 <= total_n <= away.len(),
    decreases n,
{
    if n <= 0 {
        0nat
    } else {
        let i = n - 1;
        count_host_guest_pairs(home, away, n - 1, total_n)
            + count_matches_at_i(home, away, i, total_n)
    }
}

impl Solution {
    pub fn count_host_guest_uniforms(home: Vec<i32>, away: Vec<i32>, n: usize) -> (result: usize)
        requires
            2 <= n <= 30,
            home.len() == n,
            away.len() == n,
            forall|i: int| 0 <= i < home.len() as int ==> 1 <= #[trigger] home[i] <= 100,
            forall|i: int| 0 <= i < away.len() as int ==> 1 <= #[trigger] away[i] <= 100,
            forall|i: int| 0 <= i < home.len() as int ==> home[i] as int != away[i] as int,
        ensures
            result as nat == count_host_guest_pairs(home@, away@, n as int, n as int),
    {
        let mut count = 0usize;
        let mut i = 0usize;
        while i < n {
            let mut j = 0usize;
            while j < n {
                if i != j && home[i] == away[j] {
                    count += 1;
                }
                j += 1;
            }
            i += 1;
        }
        count
    }
}

}
