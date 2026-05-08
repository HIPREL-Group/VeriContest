use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_sum(seq: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= seq.len(),
    decreases
        k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(seq, k - 1) + seq[k - 1] as int
    }
}

pub open spec fn spec_feasible(sum_time: int, min_s: Seq<i32>, max_s: Seq<i32>, d: int) -> bool {
    spec_prefix_sum(min_s, d) <= sum_time && sum_time <= spec_prefix_sum(max_s, d)
}

impl Solution {
    pub fn before_exam_schedule(
        d: usize,
        sum_time: i32,
        min_t: Vec<i32>,
        max_t: Vec<i32>,
    ) -> (res: (bool, Vec<i32>))
        requires
            (d as int) >= 1 && (d as int) <= 30,
            d == min_t.len(),
            d == max_t.len(),
            0 <= sum_time <= 240,
            forall |i: int|
                0 <= i < d as int ==> 0 <= (#[trigger] min_t@[i] as int) && (min_t@[i] as int) <= (max_t@[i] as int)
                    && (max_t@[i] as int) <= 8,
        ensures
            res.0 == spec_feasible(sum_time as int, min_t@, max_t@, d as int),
            !res.0 ==> res.1.len() == 0,
            res.0 ==> res.1.len() == d,
            res.0 ==> spec_prefix_sum(res.1@, d as int) == (sum_time as int),
            res.0 ==> forall |i: int|
                0 <= i < d as int ==> (min_t@[i] as int) <= (#[trigger] res.1@[i] as int)
                    && (res.1@[i] as int) <= (max_t@[i] as int),
    {
    }
}

}
