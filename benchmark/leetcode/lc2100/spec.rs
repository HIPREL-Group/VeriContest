use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_day(security: Seq<i32>, time: int, day: int) -> bool {
        0 <= day < security.len()
        && 0 <= time
        && time <= day
        && day + time < security.len()
        && (forall |j: int| day - time <= j < day ==> #[trigger] security[j] >= security[j + 1])
        && (forall |j: int| day <= j < day + time ==> #[trigger] security[j] <= security[j + 1])
    }

    pub fn good_days_to_rob_bank(security: Vec<i32>, time: i32) -> (result: Vec<i32>)
        requires
            1 <= security.len() <= 100_000,
            0 <= time <= 100_000,
            forall |i: int| 0 <= i < security.len() ==> 0 <= #[trigger] security[i] <= 100_000,
        ensures
            forall |k: int| 0 <= k < result@.len() ==>
                0 <= result@[k]
                && result@[k] < security.len() as i32
                && Self::good_day(security@, time as int, result@[k] as int),
            forall |day: int| 0 <= day < security.len() && Self::good_day(security@, time as int, day)
                ==> #[trigger] result@.contains(day as i32),
            forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
    {
    }
}

}
