use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum_upto(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_sum_upto(s, n - 1) + s[n - 1]
    }
}

pub open spec fn spec_battle_answer(s: Seq<i64>) -> int
    recommends
        2 <= s.len(),
{
    let n = s.len() as int;
    spec_sum_upto(s, n) - 2 * s[n - 2]
}

impl Solution {
    pub fn battle_for_survive(a: Vec<i64>) -> (res: i64)
        requires
            2 <= a.len() <= 200_000,
            forall|i: int|
                0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
        ensures
            res as int == spec_battle_answer(a@),
    {
        let n = a.len();
        let mut s = 0i64;
        let mut i = 0usize;
        while i < n {
            s = s + a[i];
            i = i + 1;
        }
        s - 2 * a[n - 2]
    }
}

}
