use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sorted(s: Seq<i64>, n: int) -> bool {
    n <= s.len() && forall|i: int| 0 <= i < n - 1 ==> #[trigger] s[i] <= s[i + 1]
}

pub open spec fn spec_sum_upto(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else { spec_sum_upto(s, n - 1) + s[n - 1] }
}

pub open spec fn spec_step(
    s: Seq<i64>, n: int, k: int, pos: int,
    botnum: int, prsnum: int, prev: int, first: bool,
) -> int
    decreases n - pos,
{
    if pos >= n {
        prsnum
    } else if pos > 0 && s[pos] == s[pos - 1] {
        spec_step(s, n, k, pos + 1, botnum, prsnum, prev, first)
    } else {
        let cnt = n - pos;
        let delta = if pos == 0 { s[0] as int } else { (s[pos] - s[pos - 1]) as int };
        let prs2 = if first { prsnum } else { prsnum + (pos - prev) };
        let prod = cnt * delta;
        if botnum + prod >= k {
            prs2 + (k - botnum)
        } else {
            spec_step(s, n, k, pos + 1, botnum + prod, prs2 + prod, pos, false)
        }
    }
}

pub open spec fn spec_answer(s: Seq<i64>, n: int, k: int) -> int {
    spec_step(s, n, k, 0, 0, 0, 0, true)
}

impl Solution {
    pub fn min_lemonade_presses(n: usize, k: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= n <= 200_000,
            n == a.len(),
            sorted(a@, n as int),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            res as int == spec_answer(a@, n as int, k as int),
    {
    }
}

}
