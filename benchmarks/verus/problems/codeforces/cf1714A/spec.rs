use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_wait_minutes(now: int, alarm: int) -> int {
        if alarm >= now {
            alarm - now
        } else {
            alarm + 1440 - now
        }
    }

    pub fn min_wait_minutes(now: i32, alarms: Vec<i32>) -> (res: i32)
        requires
            0 <= now < 1440,
            1 <= alarms.len() <= 10,
            forall|j: int| 0 <= j < alarms.len() as int ==> 0 <= #[trigger] alarms[j] < 1440,
        ensures
            0 <= res < 1440,
            exists|j: int|
                0 <= j < alarms.len() as int
                    && res as int == Self::spec_wait_minutes(now as int, alarms[j] as int),
            forall|j: int|
                0 <= j < alarms.len() as int
                    ==> res as int <= #[trigger] Self::spec_wait_minutes(now as int, alarms[j] as int),
    {
    }
}

}
