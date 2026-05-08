use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn arrival_time(d: int, s: int) -> int {
        (d + s - 1) / s
    }

    pub open spec fn count_le(dist: Seq<i32>, speed: Seq<i32>, t: int, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            Self::count_le(dist, speed, t, end - 1)
                + if Self::arrival_time(dist[end - 1] as int, speed[end - 1] as int) <= t {
                    1int
                } else {
                    0int
                }
        }
    }

    pub fn eliminate_maximum(dist: Vec<i32>, speed: Vec<i32>) -> (result: i32)
        requires
            dist.len() == speed.len(),
            1 <= dist.len() <= 100_000,
            forall |i: int| 0 <= i < dist.len() ==> 1 <= #[trigger] dist[i] <= 100_000,
            forall |i: int| 0 <= i < speed.len() ==> 1 <= #[trigger] speed[i] <= 100_000,
        ensures
            0 <= result <= dist.len(),
            forall |t: int| 0 <= t < result ==>
                Self::count_le(dist@, speed@, t, dist.len() as int) <= t,
            result < dist.len() as int ==>
                Self::count_le(dist@, speed@, result as int, dist.len() as int) > result as int,
    {
    }
}

}
