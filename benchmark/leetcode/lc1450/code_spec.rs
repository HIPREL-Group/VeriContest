use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_busy(start_time: Seq<i32>, end_time: Seq<i32>, query_time: i32, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        count_busy(start_time, end_time, query_time, n - 1)
            + if start_time[n - 1] <= query_time && query_time <= end_time[n - 1] { 1 as int } else { 0 as int }
    }
}

impl Solution {
    pub fn busy_student(start_time: Vec<i32>, end_time: Vec<i32>, query_time: i32) -> (res: i32)
        requires
            start_time.len() == end_time.len(),
            1 <= start_time.len() <= 100,
            forall |i: int| 0 <= i < start_time.len() ==>
                1 <= #[trigger] start_time[i] <= end_time[i] <= 1000,
            1 <= query_time <= 1000,
        ensures
            res as int == count_busy(start_time@, end_time@, query_time, start_time.len() as int),
    {
        let mut count: i32 = 0;
        let n = start_time.len();
        let mut i: usize = 0;
        while i < n {
            if start_time[i] <= query_time && query_time <= end_time[i] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

}
