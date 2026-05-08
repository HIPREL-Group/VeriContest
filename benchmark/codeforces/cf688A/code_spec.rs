use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn all_opponents_present(row: Seq<u8>) -> bool {
    forall|j: int| 0 <= j && j < row.len() ==> #[trigger] row[j] == 49u8
}

pub open spec fn arya_beats(row: Seq<u8>) -> bool {
    !all_opponents_present(row)
}

pub open spec fn win_interval(days: Seq<Vec<u8>>, l: int, r: int) -> bool {
    forall|t: int| l <= t && t <= r ==> #[trigger] arya_beats(days[t]@)
}

pub open spec fn win_streak_ending_at(days: Seq<Vec<u8>>, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= days.len() {
        0
    } else if !arya_beats(days[i]@) {
        0
    } else if i == 0 {
        1
    } else if arya_beats(days[i - 1]@) {
        win_streak_ending_at(days, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_win_streak_upto(days: Seq<Vec<u8>>, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = win_streak_ending_at(days, hi);
        let prev = max_win_streak_upto(days, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

pub struct Solution;

impl Solution {
    fn is_win_row(row: &Vec<u8>) -> bool {
        let n = row.len();
        let mut j = 0usize;
        let mut found = false;
        while j < n
            decreases n - j,
        {
            if row[j] == 48u8 {
                found = true;
            }
            j = j + 1;
        }
        found
    }

    pub fn max_consecutive_winning_days(n: usize, d: usize, days: &Vec<Vec<u8>>) -> (result: usize)
        requires
            1 <= n && n <= 100,
            1 <= d && d <= 100,
            days.len() == d,
            forall|i: int|
                0 <= i && i < d ==> #[trigger] days@[i].len() == n,
            forall|i: int, j: int|
                0 <= i && i < d && 0 <= j && j < n
                    ==> (#[trigger] days@[i]@[j] == 48u8 || #[trigger] days@[i]@[j] == 49u8),
        ensures
            result as int <= d as int,
            result as int == max_win_streak_upto(days@, d as int - 1),
            (result as int == 0) || (exists|l: int, r: int|
                0 <= l && l <= r && r < d as int && win_interval(days@, l, r) && r - l + 1 == result as int),
            forall|l: int, r: int|
                0 <= l && l <= r && r < d as int && win_interval(days@, l, r) ==> r - l + 1 <= result as int,
    {
        let _ = n;
        let mut best = 0usize;
        let mut cur = 0usize;
        let mut i = 0usize;
        while i < d
            decreases d - i,
        {
            if Solution::is_win_row(&days[i]) {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

}
