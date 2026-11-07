use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_gap_at_prefix(l: Seq<i64>, r: Seq<i64>, m: int, end: int) -> int
    recommends
        l.len() == r.len(),
        0 <= end <= l.len(),
    decreases end,
{
    if end <= 0 {
        if l.len() == 0 { m } else { l[0] as int }
    } else {
        let prev_gap = max_gap_at_prefix(l, r, m, end - 1);
        let new_gap = if end == l.len() { m - r[end - 1] as int } else { l[end] as int - r[end - 1] as int };
        if new_gap > prev_gap { new_gap } else { prev_gap }
    }
}

impl Solution {
    pub fn can_shower(s: i64, m: i64, l: Vec<i64>, r: Vec<i64>) -> (result: bool)
        requires
            1 <= s <= 1_000_000_000,
            1 <= m <= 1_000_000_000,
            1 <= l.len() <= 200_000,
            l.len() == r.len(),
            forall|i: int| 0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] < r[i] && r[i] <= m,
            forall|i: int| 0 < i < l.len() ==> #[trigger] l[i] > r[i - 1],
        ensures
            result == (max_gap_at_prefix(l@, r@, m as int, l.len() as int) >= s as int),
    {
        let n = l.len();
        let mut max_gap: i64 = l[0];
        let mut i: usize = 0;
        while i < n {
            let end_pos: i64 = if i + 1 == n { m } else { l[i + 1] };
            let gap = end_pos - r[i];
            if gap > max_gap {
                max_gap = gap;
            }
            i = i + 1;
        }
        max_gap >= s
    }
}

}
