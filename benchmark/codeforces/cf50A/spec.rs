use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_dominoes_spec(m: int, n: int) -> int {
    (m * n) / 2
}

impl Solution {
    pub fn max_dominoes(m: u32, n: u32) -> (result: u32)
        requires
            1 <= m <= 16,
            1 <= n <= 16,
        ensures
            result as int == max_dominoes_spec(m as int, n as int),
    {
    }
}

}
