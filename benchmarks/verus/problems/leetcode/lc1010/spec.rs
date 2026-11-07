use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_matches(s: Seq<i32>, j: int, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else if (s[j] as int + s[end - 1] as int) % 60 == 0 {
        count_matches(s, j, end - 1) + 1
    } else {
        count_matches(s, j, end - 1)
    }
}

pub open spec fn count_valid_pairs(s: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_valid_pairs(s, n - 1) + count_matches(s, n - 1, n - 1)
    }
}

impl Solution {
    pub fn num_pairs_divisible_by60(time: Vec<i32>) -> (result: i32)
        requires
            1 <= time.len() <= 60_000,
            forall|i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 500,
        ensures
            result as int == count_valid_pairs(time@, time@.len() as int),
    {
    }
}

}
