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
        let n = a.len();
        let mut i: usize = 0;
        let mut cur_k: i64 = k;
        let mut answer: u64 = 0;

        while i < n
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                0 <= i <= n + 1, 
                0 <= cur_k <= k,
                answer <= i as u64 * 1_000_000_000u64,
                forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                forall |x: int, y: int| 0 <= x <= y < a.len() ==> a[x] >= a[y],
                answer@ + Self::solve_spec(a@, k, i as int, cur_k as int) == Self::solve(a@, k),
            decreases n - i,
        {
            if i + 1 == n {
                answer = answer + a[i] as u64;
                i = i + 1;
            } else {
                let diff = a[i] - a[i + 1];
                if cur_k >= diff {
                    cur_k = cur_k - diff;
                } else {
                    answer = answer + (diff - cur_k) as u64;
                    cur_k = 0;
                }
                i = i + 2;
            }
        }

        answer
    }
}

}
