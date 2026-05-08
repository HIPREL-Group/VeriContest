use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_right_interval(intervals: Vec<Vec<i32>>) -> (res: Vec<i32>) 
        requires 
            1 <= intervals.len() <= 20_000, 
            forall |i: int| 0 <= i < intervals.len() ==> intervals[i].len() == 2, 
            forall |i: int| 0 <= i < intervals.len() ==> -1_000_000 <= #[trigger] intervals[i][0] <= intervals[i][1] <= 1_000_000,
            forall |i: int, j: int| 0 <= i < j < intervals.len() ==> intervals[i][0] != intervals[j][0], 
        ensures 
            res.len() == intervals.len(),
            forall |i: int| 0 <= i < res.len() ==> {
                ||| (res[i] == -1 && forall |j: int| 0 <= j < intervals.len() ==> intervals[j][0] < intervals[i][1])
                ||| (0 <= res[i] < intervals.len() && 
                     intervals[res[i] as int][0] >= intervals[i][1] &&
                     forall |j: int| 0 <= j < intervals.len() && #[trigger] intervals[j][0] >= intervals[i][1] 
                        ==> intervals[res[i] as int][0] <= intervals[j][0])
            }
    {
        let n = intervals.len();
        let mut result: Vec<i32> = Vec::new();
        for i in 0..n
            invariant
                1 <= intervals.len() <= 20_000, 
                forall |i: int| 0 <= i < intervals.len() ==> intervals[i].len() == 2, 
                forall |i: int| 0 <= i < intervals.len() ==> -1_000_000 <= #[trigger] intervals[i][0] <= intervals[i][1] <= 1_000_000,
                forall |i: int, j: int| 0 <= i < j < intervals.len() ==> #[trigger] intervals[i][0] != #[trigger] intervals[j][0], 
                intervals.len() == n, 
                result.len() == i,
                forall |k: int| 0 <= k < i ==> {
                    ||| (result[k] == -1 && forall |j: int| 0 <= j < n ==> intervals[j][0] < intervals[k][1])
                    ||| (0 <= result[k] < n && 
                         intervals[result[k] as int][0] >= intervals[k][1] &&
                         forall |j: int| 0 <= j < n && #[trigger] intervals[j][0] >= intervals[k][1] 
                            ==> intervals[result[k] as int][0] <= intervals[j][0])
                }
        {
            let mut min_start: i32 = 1_000_001;
            let mut ans: i32 = -1;

            for j in 0..n
                invariant
                    1 <= intervals.len() <= 20_000, 
                    forall |i: int| 0 <= i < intervals.len() ==> intervals[i].len() == 2, 
                    forall |i: int| 0 <= i < intervals.len() ==> -1_000_000 <= #[trigger] intervals[i][0] <= intervals[i][1] <= 1_000_000,
                    forall |i: int, j: int| 0 <= i < j < intervals.len() ==> #[trigger] intervals[i][0] != #[trigger] intervals[j][0], 
                    intervals.len() == n, 
                    -1_000_000 <= min_start <= 1_000_001,
                    0 <= i < n, 
                    ans == -1 || (0 <= ans < n && intervals[ans as int][0] == min_start),
                    ans == -1 ==> min_start == 1_000_001,
                    ans != -1 ==> (min_start >= intervals[i as int][1] && intervals[ans as int][0] >= intervals[i as int][1]),
                    forall |k: int| 0 <= k < j && intervals[k][0] >= intervals[i as int][1] ==> min_start <= intervals[k][0],
            {
                if intervals[j][0] >= intervals[i][1] && intervals[j][0] < min_start {
                    min_start = intervals[j][0];
                    ans = j as i32;
                }
            }

            result.push(ans);
        }

        result
    }
}

}