use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_seq_sum(s: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= s.len(),
    decreases k as nat,
{
    if k <= 0 {
        0int
    } else {
        spec_seq_sum(s, k - 1) + (s[k - 1] as int)
    }
}

pub open spec fn spec_partial_sum(i: int, b: int, r: int) -> int
    recommends
        0 <= i,
        0 <= r,
{
    if i <= r {
        i * (b + 1)
    } else {
        r * (b + 1) + (i - r) * b
    }
}

pub open spec fn spec_seq_max(s: Seq<i32>, k: int) -> int
    recommends
        0 < k <= s.len(),
{
    s.take(k).map_values(|x| x as int).max()
}

pub open spec fn spec_seq_min(s: Seq<i32>, k: int) -> int
    recommends
        0 < k <= s.len(),
{
    s.take(k).map_values(|x| x as int).min()
}

pub open spec fn spec_valid_candy_split(s: Seq<i32>, n: int, m: int) -> bool {
    s.len() == m && spec_seq_sum(s, m) == n && forall|j: int|
        0 <= j < m ==> (#[trigger] s[j] as int) >= 1
}

impl Solution {
    pub fn fair_candy_split(n: i32, m: i32) -> (result: Vec<i32>)
        requires
            1 <= m <= n <= 100,
        ensures
            spec_valid_candy_split(result@, n as int, m as int),
            exists|t: Seq<i32>|
                spec_valid_candy_split(t, n as int, m as int) && t == result@,
            forall|s: Seq<i32>|
                spec_valid_candy_split(s, n as int, m as int) ==> {
                    let spread_s = spec_seq_max(s, m as int) - spec_seq_min(s, m as int);
                    let spread_r = spec_seq_max(result@, m as int) - spec_seq_min(result@, m as int);
                    spread_s >= spread_r
                },
    {
        let base = n / m;
        let rem = n % m;
        let mut v: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mu = m as usize;
        while i < mu {
            let val = if i < rem as usize { base + 1 } else { base };
            v.push(val);
            i = i + 1;
        }
        v
    }
}

}
