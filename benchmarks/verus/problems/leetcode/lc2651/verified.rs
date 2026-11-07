use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn arrival_spec(arrival: int, delayed: int) -> int {
        (arrival + delayed) % 24
    }

    pub fn find_delayed_arrival_time(arrival_time: i32, delayed_time: i32) -> (result: i32)
        requires
            1 <= arrival_time < 24,
            1 <= delayed_time <= 24,
        ensures
            result == Self::arrival_spec(arrival_time as int, delayed_time as int),
    {
        (arrival_time + delayed_time) % 24
    }
}

}
