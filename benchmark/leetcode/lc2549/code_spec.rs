use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn distinct_integers_spec(n: int) -> int
        recommends
            1 <= n <= 100,
    {
        if n == 1 { 1 } else { n - 1 }
    }

    pub fn distinct_integers(n: i32) -> (result: i32)
        requires
            1 <= n <= 100,
        ensures
            result as int == Self::distinct_integers_spec(n as int),
            1 <= result as int <= n as int,
    {
        if n == 1 {
            1
        } else {
            n - 1
        }
    }
}

}
