use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn maximum_achievable_spec(num: int, t: int) -> int {
        num + 2 * t
    }

        pub fn the_maximum_achievable_x(num: i32, t: i32) -> (result: i32)
        requires
            1 <= num <= 50,
            1 <= t <= 50,
        ensures
            result as int == Self::maximum_achievable_spec(num as int, t as int),
    {
    }
}

}
