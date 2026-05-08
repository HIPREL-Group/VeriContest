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
        let mut sum: u64 = 0;
        let mut i: u32 = 2;
        while i < n {
            let i64v: u64 = i as u64;
            let term: u64 = i64v * (i64v + 1);
            sum = sum + term;
            i = i + 1;
        }
        sum
    }
}

}
