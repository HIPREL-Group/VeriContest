use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_eligible_threshold(k: int) -> int {
    5 - k
}

pub open spec fn spec_is_eligible(y: int, k: int) -> bool {
    y <= spec_eligible_threshold(k)
}

pub open spec fn spec_count_eligible(s: Seq<i64>, n: int, k: int) -> int
    recommends 0 <= n <= s.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_count_eligible(s, n - 1, k)
            + if spec_is_eligible(s[n - 1] as int, k) {
                1int
            } else {
                0int
            }
    }
}

impl Solution {
    pub fn max_teams(n: usize, k: i32, y: Vec<i64>) -> (result: i32)
        requires
            1 <= n <= 2000,
            n == y.len(),
            1 <= (k as int) <= 5,
            forall|i: int|
                0 <= i < n as int ==> 0 <= (#[trigger] y[i] as int) <= 5,
        ensures
            result as int == spec_count_eligible(y@, n as int, k as int) / 3,
    {
    }
}

}
