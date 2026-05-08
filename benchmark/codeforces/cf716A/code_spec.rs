use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_screen(
    t: Seq<i64>, n: int, c: int, i: int, cnt: int,
) -> int
    decreases n - i,
{
    if i >= n {
        cnt
    } else {
        let gap = t[i] - t[i - 1];
        let new_cnt = if gap <= c { cnt + 1 } else { 1 };
        spec_screen(t, n, c, i + 1, new_cnt)
    }
}

pub open spec fn spec_answer(t: Seq<i64>, n: int, c: int) -> int {
    spec_screen(t, n, c, 1, 1)
}

impl Solution {
    pub fn remaining_words(n: usize, c: i64, t: Vec<i64>) -> (res: usize)
        requires
            1 <= n <= 100_000,
            n == t.len(),
            1 <= c <= 1_000_000_000,
            forall|u: int| 0 <= u < n as int - 1 ==> #[trigger] t[u] < t[u + 1],
            forall|u: int| 0 <= u < n as int ==> 1 <= #[trigger] t[u] <= 1_000_000_000,
        ensures
            res as int == spec_answer(t@, n as int, c as int),
    {
        let mut cnt = 1usize;
        let mut i = 1usize;
        while i < n {
            if t[i] - t[i - 1] <= c {
                cnt = cnt + 1;
            } else {
                cnt = 1;
            }
            i = i + 1;
        }
        cnt
    }
}

}
