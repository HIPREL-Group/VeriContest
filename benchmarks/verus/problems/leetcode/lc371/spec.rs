use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_sum(a: i32, b: i32) -> (res: i32)
        requires
            -1000 <= a <= 1000,
            -1000 <= b <= 1000,
        ensures
            res as int == a as int + b as int,
    {
    }
}

}
