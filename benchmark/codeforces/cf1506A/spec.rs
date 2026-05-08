use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn row_of_x(x: int, n: int) -> int {
    (x - 1) % n + 1
}

pub open spec fn col_of_x(x: int, n: int) -> int {
    (x - 1) / n + 1
}

impl Solution {
    pub fn strange_table_number(n: u64, m: u64, x: u64) -> (result: u64)
        requires
            1 <= n <= 1_000_000,
            1 <= m <= 1_000_000,
            1 <= x <= n * m,
        ensures
            result as int == (row_of_x(x as int, n as int) - 1) * m as int + col_of_x(x as int, n as int),
    {
    }
}

}
