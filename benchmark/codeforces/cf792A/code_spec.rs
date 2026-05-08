use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_min_gap(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 2 {
        s[1] - s[0]
    } else {
        let g = s[n - 1] - s[n - 2];
        let m = spec_min_gap(s, n - 1);
        if g < m {
            g
        } else {
            m
        }
    }
}

pub open spec fn spec_count_gaps_eq(s: Seq<i64>, n: int, d: int) -> int
    decreases n,
{
    if n < 2 {
        0
    } else {
        let tail = if s[n - 1] - s[n - 2] == d {
            1int
        } else {
            0int
        };
        if n == 2 {
            tail
        } else {
            spec_count_gaps_eq(s, n - 1, d) + tail
        }
    }
}

pub open spec fn spec_scan(s: Seq<i64>, n: int, k: int, min_d: int, cnt: int) -> (int, int)
    decreases n - k,
{
    if k >= n - 1 {
        (min_d, cnt)
    } else {
        let d = s[k + 1] - s[k];
        if d < min_d {
            spec_scan(s, n, k + 1, d, 1)
        } else if d == min_d {
            spec_scan(s, n, k + 1, min_d, cnt + 1)
        } else {
            spec_scan(s, n, k + 1, min_d, cnt)
        }
    }
}

pub open spec fn spec_answer(s: Seq<i64>, n: int) -> (int, int) {
    (spec_min_gap(s, n), spec_count_gaps_eq(s, n, spec_min_gap(s, n)))
}

impl Solution {
    pub fn min_gap_and_count(n: usize, a: Vec<i64>) -> (res: (i64, i64))
        requires
            2 <= n <= 200_000,
            n == a.len(),
            forall|u: int|
                0 <= u < n as int - 1 ==> #[trigger] a[u] < a[u + 1],
            forall|u: int|
                0 <= u < n as int ==> -1_000_000_000 <= #[trigger] a[u] && a[u] <= 1_000_000_000,
        ensures
            (res.0 as int, res.1 as int) == spec_scan(a@, n as int, 1, a@[1] - a@[0], 1),
    {
        let mut min_d = a[1] - a[0];
        let mut cnt: i64 = 1;
        let mut k: usize = 1;
        while k < n - 1
            decreases n - 1 - k,
        {
            let d = a[k + 1] - a[k];
            if d < min_d {
                min_d = d;
                cnt = 1;
            } else if d == min_d {
                cnt = cnt + 1;
            }
            k = k + 1;
        }
        (min_d, cnt)
    }
}

}
