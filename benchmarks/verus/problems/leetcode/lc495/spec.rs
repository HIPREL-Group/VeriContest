use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(ts: Seq<i32>, duration: int, i: nat, total: int) -> int
        recommends i <= ts.len(),
        decreases ts.len() - i,
    {
        if i >= ts.len() {
            total
        } else if i + 1 >= ts.len() {
            total + duration
        } else {
            let gap = (ts[(i + 1) as int] as int) - (ts[i as int] as int);
            let contrib = if gap < duration { gap } else { duration };
            Self::scan_spec(ts, duration, i + 1, total + contrib)
        }
    }

    pub open spec fn find_poisoned_duration_spec(ts: Seq<i32>, duration: int) -> int {
        if ts.len() == 0 { 0 } else { Self::scan_spec(ts, duration, 0, 0) }
    }

    pub fn find_poisoned_duration(time_series: Vec<i32>, duration: i32) -> (res: i32)
        requires
            1 <= time_series.len() <= 10_000,
            0 <= duration <= 10_000_000,
            forall |j: int| 0 <= j < time_series@.len() ==> 0 <= #[trigger] time_series@[j] <= 10_000_000i32,
            forall |j: int| 0 <= j < time_series@.len() - 1 ==>
                #[trigger] time_series@[j] <= time_series@[j + 1],
            Self::find_poisoned_duration_spec(time_series@, duration as int) <= i32::MAX as int,
        ensures
            res as int == Self::find_poisoned_duration_spec(time_series@, duration as int),
    {
    }
}

} 
