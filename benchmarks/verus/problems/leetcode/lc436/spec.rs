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
        
    }
}

}