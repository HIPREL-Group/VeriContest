use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn capped_trips_prefix(time: Seq<i32>, t: int, cap: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            let prev = Self::capped_trips_prefix(time, t, cap, n - 1);
            let s = prev + t / (time[n - 1] as int);
            if s >= cap { cap } else { s }
        }
    }

    pub open spec fn feasible(time: Seq<i32>, t: int, total: int) -> bool {
        Self::capped_trips_prefix(time, t, total, time.len() as int) == total
    }

    pub fn minimum_time(time: Vec<i32>, total_trips: i32) -> (ans: i64)
        requires
            1 <= time.len() <= 100000,
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            1 <= total_trips <= 10000000,
        ensures
            1 <= ans <= 100000000000000,
            Self::feasible(time@, ans as int, total_trips as int),
            forall |t: int| 1 <= t < ans ==> !#[trigger] Self::feasible(time@, t, total_trips as int),
    {
    }
}

}
