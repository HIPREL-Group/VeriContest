use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn advances(score: int, threshold: int) -> bool {
    score >= threshold && score > 0
}

pub open spec fn count_advancing_to(scores: Seq<i32>, threshold: int, end: int) -> nat
    recommends
        0 <= end <= scores.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_advancing_to(scores, threshold, end - 1)
            + if advances(scores[end - 1] as int, threshold) {
                1nat
            } else {
                0nat
            }
    }
}

pub open spec fn count_advancing(scores: Seq<i32>, k: int) -> nat
    recommends
        1 <= k <= scores.len(),
{
    count_advancing_to(scores, scores[k - 1] as int, scores.len() as int)
}

impl Solution {
    pub fn count_advancing(scores: Vec<i32>, k: usize) -> (result: usize)
        requires
            1 <= scores.len() <= 50,
            1 <= k <= scores.len(),
            forall |i: int| 0 <= i < scores.len() ==> 0 <= #[trigger] scores[i] <= 100,
            forall |i: int| 0 <= i < scores.len() - 1 ==> #[trigger] scores[i] >= scores[i + 1],
        ensures
            result as int == count_advancing(scores@, k as int),
    {
    }
}

}
