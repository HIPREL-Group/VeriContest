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
        let n = intervals.len();
        let mut count: i32 = 0;

        for i in 0..n
            invariant
                n == intervals.len(),
                1 <= n <= 1000,
                0 <= count as int <= i as int,
                count as int == Self::count_not_covered(intervals@, i as int),
                forall |k: int| 0 <= k < n ==>
                    (#[trigger] intervals[k]).len() == 2,
                forall |k: int| 0 <= k < n ==>
                    0 <= (#[trigger] intervals[k])[0] < intervals[k][1] <= 100_000,
        {
            let mut covered = false;
            for j in 0..n
                invariant
                    n == intervals.len(),
                    1 <= n <= 1000,
                    0 <= i < n,
                    covered == (exists |k: int| 0 <= k < j as int && k != i as int &&
                        intervals[k][0] <= intervals[i as int][0] &&
                        intervals[i as int][1] <= intervals[k][1]),
                    forall |k: int| 0 <= k < n ==>
                        (#[trigger] intervals[k]).len() == 2,
                    forall |k: int| 0 <= k < n ==>
                        0 <= (#[trigger] intervals[k])[0] < intervals[k][1] <= 100_000,
            {
                if j != i && intervals[j][0] <= intervals[i][0] && intervals[i][1] <= intervals[j][1] {
                    covered = true;
                }
            }

            if !covered {
                count += 1;
            }
        }
        count
    }
}

}
