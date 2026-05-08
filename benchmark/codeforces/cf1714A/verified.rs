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
        let mut best_idx: usize = 0;
        let mut i: usize = 1;
        while i < n
            invariant
                0 <= now < 1440,
                n == alarms.len(),
                1 <= n <= 10,
                1 <= i <= n,
                forall|j: int| 0 <= j < alarms.len() as int ==> 0 <= #[trigger] alarms[j] < 1440,
                0 <= best < 1440,
                best_idx < i,
                best as int == Self::spec_wait_minutes(now as int, alarms[best_idx as int] as int),
                forall|j: int|
                    0 <= j < i as int
                        ==> best as int <= #[trigger] Self::spec_wait_minutes(now as int, alarms[j] as int),
            decreases n - i,
        {
            let old_best = best;
            let d = Self::wait_minutes(now, alarms[i]);
            if d < best {
                best = d;
                best_idx = i;
            }
            proof {
                assert(d as int == Self::spec_wait_minutes(now as int, alarms[i as int] as int));
                if d < old_best {
                    assert(best == d);
                } else {
                    assert(best == old_best);
                    assert(old_best as int <= d as int);
                }
                assert(best as int <= d as int);
                assert forall|j: int|
                    0 <= j < i as int + 1 implies best as int <= #[trigger] Self::spec_wait_minutes(now as int, alarms[j] as int) by {
                    if j < i as int {
                        assert(old_best as int <= Self::spec_wait_minutes(now as int, alarms[j] as int));
                        assert(best as int <= old_best as int);
                    } else {
                        assert(j == i as int);
                        assert(best as int <= d as int);
                    }
                };
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(best_idx < alarms.len());
        }
        best
    }
}

}
