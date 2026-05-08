use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_greedy(s: Seq<i32>, m: int, k: int, i: int, cnt: int, skip: int) -> int
    decreases s.len() as int - i,
{
    if i < 0 || i >= s.len() as int || m <= 0 || k <= 0 {
        0
    } else if skip > 0 {
        spec_greedy(s, m, k, i + 1, 0, skip - 1)
    } else if s[i] == 0 {
        if cnt + 1 >= m {
            1 + spec_greedy(s, m, k, i + 1, 0, k - 1)
        } else {
            spec_greedy(s, m, k, i + 1, cnt + 1, 0)
        }
    } else {
        spec_greedy(s, m, k, i + 1, 0, 0)
    }
}

impl Solution {
    pub fn min_timar_operations(s: Vec<i32>, m: usize, k: usize) -> (res: i64)
        requires
            1 <= s.len() <= 200_000,
            1 <= (m as int) <= s.len() as int,
            1 <= (k as int) <= s.len() as int,
            forall|t: int| 0 <= t < s.len() as int ==> #[trigger] s[t] == 0 || s[t] == 1,
        ensures
            0 <= (res as int),
            (res as int) == spec_greedy(s@, m as int, k as int, 0, 0, 0),
    {
    }
}

}
