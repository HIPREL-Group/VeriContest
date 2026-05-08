use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn f_value(n: int) -> int
    decreases n,
{
    if n <= 0 {
        0int
    } else if n % 2 == 0 {
        f_value(n - 1) + n
    } else {
        f_value(n - 1) - n
    }
}

impl Solution {
    pub fn calculating_function(n: i64) -> (result: i64)
        requires
            1 <= n <= 1000000000000000,
        ensures
            result as int == f_value(n as int),
    {
    }
}

}
