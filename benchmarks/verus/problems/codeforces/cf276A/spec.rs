use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn joy_value(f: int, t: int, k: int) -> int {
        if t <= k {
            f
        } else {
            f - t + k
        }
    }

    pub fn max_lunch_joy(restaurants: Vec<(i64, i64)>, k: i64) -> (result: i64)
        requires
            restaurants.len() >= 1,
            restaurants.len() <= 10000,
            1 <= k <= 1000000000,
            forall |i: int| 0 <= i < restaurants.len() ==>
                1 <= #[trigger] restaurants@[i].0 <= 1000000000,
            forall |i: int| 0 <= i < restaurants.len() ==>
                1 <= #[trigger] restaurants@[i].1 <= 1000000000,
        ensures
            forall |i: int| 0 <= i < restaurants.len() ==>
                result >= Self::joy_value(restaurants@[i].0 as int, restaurants@[i].1 as int, k as int),
            exists |i: int| 0 <= i < restaurants.len() &&
                result == Self::joy_value(restaurants@[i].0 as int, restaurants@[i].1 as int, k as int),
    {
    }
}

}
