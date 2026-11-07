use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn damaged(i: int, k: int, l: int, m: int, n: int) -> bool {
    i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0
}

pub open spec fn count_damaged_spec(k: int, l: int, m: int, n: int, d: int) -> int
    decreases d,
{
    if d < 1 {
        0
    } else {
        let add: int = if damaged(d, k, l, m, n) { 1int } else { 0int };
        add + count_damaged_spec(k, l, m, n, d - 1)
    }
}

impl Solution {
    pub fn count_damaged(k: i32, l: i32, m: i32, n: i32, d: i32) -> (result: i32)
        requires
            1 <= k <= 10,
            1 <= l <= 10,
            1 <= m <= 10,
            1 <= n <= 10,
            1 <= d <= 100_000,
        ensures
            result as int == count_damaged_spec(k as int, l as int, m as int, n as int, d as int),
    {
    }
}

}
