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

    pub fn wait_minutes(now: i32, alarm: i32) -> (res: i32)
        requires
            0 <= now < 1440,
            0 <= alarm < 1440,
        ensures
            res as int == Self::spec_wait_minutes(now as int, alarm as int),
            0 <= res < 1440,
    {
        if alarm >= now {
            alarm - now
        } else {
            alarm + 1440 - now
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
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
        let n = alarms.len();
        let mut best = Self::wait_minutes(now, alarms[0]);
        let mut i: usize = 1;
        while i < n {
            let d = Self::wait_minutes(now, alarms[i]);
            if d < best {
                best = d;
            }
            i = i + 1;
        }
        best
    }
}

}
