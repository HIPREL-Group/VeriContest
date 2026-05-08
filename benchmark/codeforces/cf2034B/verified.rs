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
        let n = s.len();
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let mut cnt: usize = 0;
        let mut skip: usize = 0;
        while i < n
            invariant
                n == s.len(),
                n <= 200_000,
                1 <= (m as int) <= n as int,
                1 <= (k as int) <= n as int,
                i <= n,
                0 <= (cnt as int) < (m as int),
                skip <= n,
                0 <= (ans as int) <= (i as int),
                forall|t: int| 0 <= t < n as int ==> #[trigger] s@[t] == 0 || s@[t] == 1,
                (ans as int) + spec_greedy(s@, m as int, k as int, i as int, cnt as int, skip as int)
                    == spec_greedy(s@, m as int, k as int, 0, 0, 0),
            decreases n - i,
        {
            if skip > 0 {
                skip = skip - 1;
                cnt = 0;
            } else if s[i] == 0 {
                if cnt + 1 == m {
                    ans = ans + 1;
                    cnt = 0;
                    skip = k - 1;
                } else {
                    cnt = cnt + 1;
                }
            } else {
                cnt = 0;
            }
            i = i + 1;
        }
        ans
    }
}

}
