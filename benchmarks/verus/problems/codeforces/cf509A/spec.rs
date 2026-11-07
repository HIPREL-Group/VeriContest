use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn table_value(n: int, i: int, j: int) -> int
    decreases i + j,
{
    if i < 0 || j < 0 || i >= n || j >= n {
        0int
    } else if i == 0 || j == 0 {
        1int
    } else {
        table_value(n, i - 1, j) + table_value(n, i, j - 1)
    }
}

impl Solution {
    pub fn max_in_table(n: u32) -> (result: u32)
        requires
            1 <= n <= 10,
        ensures
            result as int == table_value(n as int, (n - 1) as int, (n - 1) as int),
    {
    }
}

}
