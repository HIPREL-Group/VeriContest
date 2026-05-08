use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn triangulation_sum(n: int) -> int
    decreases n,
{
    if n <= 2 {
        0int
    } else {
        triangulation_sum(n - 1) + (n - 1) * n
    }
}

impl Solution {
    pub fn min_triangulation(n: u32) -> (res: u64)
        requires
            3 <= n <= 500,
        ensures
            res as int == triangulation_sum(n as int),
    {
    }
}

}
