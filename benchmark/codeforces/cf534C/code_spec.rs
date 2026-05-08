use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_maxima(maxima: Seq<i64>, end: int) -> int
    recommends 0 <= end <= maxima.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        sum_maxima(maxima, end - 1) + maxima[end - 1] as int
    }
}

pub open spec fn other_sum_possible(maxima: Seq<i64>, i: int, rem: int) -> bool
    recommends 0 <= i < maxima.len(),
{
    maxima.len() - 1 <= rem <= sum_maxima(maxima, maxima.len() as int) - maxima[i] as int
}

pub open spec fn die_value_possible(maxima: Seq<i64>, total: int, i: int, x: int) -> bool
    recommends 0 <= i < maxima.len(),
{
    1 <= x <= maxima[i] as int && other_sum_possible(maxima, i, total - x)
}

pub open spec fn impossible_count_upto(maxima: Seq<i64>, total: int, i: int, limit: int) -> int
    recommends 0 <= i < maxima.len(), 0 <= limit <= maxima[i] as int,
    decreases limit,
{
    if limit <= 0 {
        0
    } else {
        impossible_count_upto(maxima, total, i, limit - 1)
            + if die_value_possible(maxima, total, i, limit) { 0int } else { 1int }
    }
}

pub open spec fn impossible_count(maxima: Seq<i64>, total: int, i: int) -> int
    recommends 0 <= i < maxima.len(),
{
    impossible_count_upto(maxima, total, i, maxima[i] as int)
}

impl Solution {
    pub fn impossible_face_counts(total: i64, maxima: Vec<i64>) -> (res: Vec<i64>)
        requires
            1 <= maxima.len() <= 200_000,
            forall|i: int| 0 <= i < maxima.len() ==> 1 <= #[trigger] maxima[i] <= 1_000_000,
            maxima.len() as int <= total as int <= sum_maxima(maxima@, maxima.len() as int),
        ensures
            res.len() == maxima.len(),
            forall|i: int| 0 <= i < res.len() ==> res[i] as int == impossible_count(maxima@, total as int, i),
    {
        let n = maxima.len();
        let mut sum_all = 0i64;
        let mut i = 0usize;
        while i < n
        {
            sum_all += maxima[i];
            i += 1;
        }
        let mut res = Vec::new();
        i = 0;
        while i < n
        {
            let mut lo = total - (sum_all - maxima[i]);
            if lo < 1 {
                lo = 1;
            }
            let mut hi = total - (n as i64 - 1);
            if hi > maxima[i] {
                hi = maxima[i];
            }
            let bad = if hi < lo {
                maxima[i]
            } else if hi == maxima[i] {
                lo - 1
            } else {
                lo - 1 + maxima[i] - hi
            };
            res.push(bad);
            i += 1;
        }
        res
    }
}

}
