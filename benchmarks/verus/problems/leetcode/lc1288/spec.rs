use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_covered(intervals: Seq<Vec<i32>>, i: int) -> bool {
        exists |j: int| 0 <= j < intervals.len() && j != i &&
            intervals[j][0] <= intervals[i][0] && intervals[i][1] <= intervals[j][1]
    }

    pub open spec fn count_not_covered(intervals: Seq<Vec<i32>>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            Self::count_not_covered(intervals, end - 1) +
            if !Self::is_covered(intervals, end - 1) { 1int } else { 0int }
        }
    }

    pub fn remove_covered_intervals(intervals: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= intervals.len() <= 1000,
            forall |i: int| 0 <= i < intervals.len() ==>
                (#[trigger] intervals[i]).len() == 2,
            forall |i: int| 0 <= i < intervals.len() ==>
                0 <= (#[trigger] intervals[i])[0] < intervals[i][1] <= 100_000,
            forall |i: int, j: int| 0 <= i < j < intervals.len() ==>
                !(intervals[i][0] == intervals[j][0] && intervals[i][1] == intervals[j][1]),
        ensures
            0 <= res <= intervals.len(),
            res as int == Self::count_not_covered(intervals@, intervals.len() as int),
    {
    }
}

}
