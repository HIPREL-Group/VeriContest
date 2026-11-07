use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn sum_of_three(num: i64) -> (result: Vec<i64>)
        requires
            0 <= num <= 1000000000000000,
        ensures
            if num % 3 == 0 {
                result.len() == 3
                    && result[0] + result[1] + result[2] == num
                    && result[1] == result[0] + 1
                    && result[2] == result[1] + 1
            } else {
                result.len() == 0
            },
    {
    }
}

}
