use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_minutes_before_new_year(h: int, m: int) -> int {
    1440 - 60 * h - m
}

impl Solution {
    pub fn minutes_before_new_year_one(h: i32, m: i32) -> (result: i32)
        requires
            0 <= h < 24,
            0 <= m < 60,
            !(h == 0 && m == 0),
        ensures
            result as int == spec_minutes_before_new_year(h as int, m as int),
    {
        proof {
            let hi = h as int;
            let mi = m as int;
            assert(0 <= hi && hi < 24);
            assert(0 <= mi && mi < 60);
            assert(60 * hi + mi < 1440);
        }
        let result = (1440i64 - 60i64 * (h as i64) - (m as i64)) as i32;
        proof {
            assert(result as int == 1440 - (h as int) * 60 - (m as int));
            assert(result as int == spec_minutes_before_new_year(h as int, m as int));
        }
        result
    }
}

}
