use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn sum(num1: i32, num2: i32) -> (result: i32)
        requires
            -100 <= num1 <= 100,
            -100 <= num2 <= 100,
        ensures
            result as int == num1 as int + num2 as int,
    {
    }
}

}
