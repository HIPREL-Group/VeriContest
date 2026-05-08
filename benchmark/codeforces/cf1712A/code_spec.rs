use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn bad_prefix_count(s: Seq<i32>, hi: int, t: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0int
    } else {
        (if s[hi - 1] > t { 1int } else { 0int }) + bad_prefix_count(s, hi - 1, t)
    }
}

impl Solution {
    pub fn min_swaps_minimize_prefix_sum(p: Vec<i32>, n: usize, k: usize) -> (result: i32)
        requires
            p.len() == n,
            1 <= k <= n <= 100,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] && p[i] <= n as int,
        ensures
            (result as int) == bad_prefix_count(p@, k as int, k as int),
            0 <= (result as int) && (result as int) <= k as int,
    {
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < k
            decreases k - i,
        {
            if p[i] > k as i32 {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}

}
