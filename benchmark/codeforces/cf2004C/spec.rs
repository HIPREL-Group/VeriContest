use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn solve_spec(a: Seq<i64>, k: i64, i: int, cur_k: int) -> nat
        recommends 0 <= i, i <= a.len() + 1,
        decreases a.len() - i,
    {
        if i >= a.len() {
            0nat
        } else if i + 1 == a.len() {
            (a[i]) as nat
        } else {
            let diff = a[i] - a[i + 1];
            if cur_k >= diff {
                Self::solve_spec(a, k, i + 2, cur_k - diff)
            } else {
                (diff - cur_k) as nat + Self::solve_spec(a, k, i + 2, 0)
            }
        }
    }

    pub open spec fn solve(a: Seq<i64>, k: i64) -> nat {
        Self::solve_spec(a, k, 0, k as int)
    }

    pub fn optimal_score(a: Vec<i64>, k: i64) -> (ans: u64)
        requires
            1 <= a.len() <= 200_000,
            0 <= k <= 1_000_000_000_000_000,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
            forall |x: int, y: int| 0 <= x <= y < a.len() ==> a[x] >= a[y],
        ensures
            ans@ == Self::solve(a@, k),
    {
    }
}

}
