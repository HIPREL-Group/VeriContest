use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min2(x: int, y: int) -> int {
    if x < y { x } else { y }
}

pub open spec fn min_suffix_sum(a: Seq<i64>, b: Seq<i64>, start: int, end: int) -> int
    recommends
        0 <= start <= end <= a.len(),
        a.len() == b.len(),
    decreases end - start,
{
    if start >= end {
        0int
    } else {
        min2(a[start] as int, b[start] as int) + min_suffix_sum(a, b, start + 1, end)
    }
}

pub open spec fn cost_at(a: Seq<i64>, b: Seq<i64>, j: int) -> int
    recommends
        0 <= j < a.len(),
        a.len() == b.len(),
{
    a[j] as int + min_suffix_sum(a, b, j + 1, a.len() as int)
}

pub open spec fn min_cost(a: Seq<i64>, b: Seq<i64>, m: int) -> int
    recommends
        1 <= m <= a.len(),
        a.len() == b.len(),
    decreases m,
{
    if m <= 1 {
        cost_at(a, b, 0)
    } else {
        let prev = min_cost(a, b, m - 1);
        let cur = cost_at(a, b, m - 1);
        if cur < prev { cur } else { prev }
    }
}

impl Solution {
    pub fn min_coins(a: Vec<i64>, b: Vec<i64>, m: usize) -> (result: i64)
        requires
            1 <= m <= a.len() <= 200_000,
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1_000_000_000,
        ensures
            result as int == min_cost(a@, b@, m as int),
    {
        let n = a.len();
        let mut suffix: Vec<i64> = Vec::with_capacity(n + 1);
        let mut k: usize = 0;
        while k <= n {
            suffix.push(0);
            k = k + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let m_val: i64 = if a[i] < b[i] { a[i] } else { b[i] };
            suffix.set(i, suffix[i + 1] + m_val);
        }
        let mut best: i64 = a[0] + suffix[1];
        let mut j: usize = 1;
        while j < m {
            let cost: i64 = a[j] + suffix[j + 1];
            if cost < best {
                best = cost;
            }
            j = j + 1;
        }
        best
    }
}

}
