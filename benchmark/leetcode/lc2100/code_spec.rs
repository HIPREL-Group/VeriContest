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
        let n = security.len();
        let mut inc_prefix: Vec<i32> = Vec::new();
        let mut dec_prefix: Vec<i32> = Vec::new();
        inc_prefix.push(0);
        dec_prefix.push(0);

        let mut i: usize = 1;
        while i < n {
            let mut inc_next = inc_prefix[i - 1];
            let prev = security[i - 1];
            let curr = security[i];
            if prev < curr {
                inc_next = inc_next + 1;
            }

            let mut dec_next = dec_prefix[i - 1];
            if prev > curr {
                dec_next = dec_next + 1;
            }

            inc_prefix.push(inc_next);
            dec_prefix.push(dec_next);

            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut day: usize = 0;
        while day < n {
            let day_i = day as i32;
            if time <= day_i
                && day_i + time < n as i32
                && inc_prefix[day] == inc_prefix[(day_i - time) as usize]
                && dec_prefix[(day_i + time) as usize] == dec_prefix[day]
            {
                result.push(day_i);
            }
            day += 1;
        }

        result
    }
}

}
