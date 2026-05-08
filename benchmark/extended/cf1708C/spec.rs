use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn compute_ans(a: Seq<i64>, q: i64, i: int, cur_q: nat) -> Seq<u8>
        recommends 0 <= i <= a.len(),
        decreases i,
    {
        if i <= 0 {
            Seq::empty()
        } else {
            let idx = i - 1;
            if a[idx] <= cur_q {
                Self::compute_ans(a, q, idx, cur_q).push(1u8)
            } else if cur_q < q {
                Self::compute_ans(a, q, idx, cur_q + 1nat).push(1u8)
            } else {
                Self::compute_ans(a, q, idx, cur_q).push(0u8)
            }
        }
    }

    pub open spec fn solve(a: Seq<i64>, q: i64) -> Seq<u8> {
        Self::compute_ans(a, q, a.len() as int, 0nat)
    }

    pub fn optimal_tests(a: Vec<i64>, q: i64) -> (ans: Vec<u8>)
        requires
            1 <= a.len() <= 100_000,
            1 <= q <= 1_000_000_000,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        ensures
            ans@ == Self::solve(a@, q),
    {
    }
}

}
