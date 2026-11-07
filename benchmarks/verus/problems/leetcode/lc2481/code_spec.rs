use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn number_of_cuts(n: i32) -> (result: i32)
        requires
            1 <= n <= 100,
        ensures
            result as int
                == if n == 1 {
                    0int
                } else if n % 2 == 0 {
                    n as int / 2
                } else {
                    n as int
                },
    {
        if n == 1 {
            0
        } else if n % 2 == 0 {
            n / 2
        } else {
            n
        }
    }
}

}
