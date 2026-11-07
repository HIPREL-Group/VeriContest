use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    pub open spec fn count_prefix(m: int, n: int, x: int, i: int) -> int
        decreases if i < 0 { 0nat } else { i as nat },
    {
        if i <= 0 || m <= 0 || n <= 0 || x < 0 {
            0
        } else {
            Self::count_prefix(m, n, x, i - 1) + Self::min2(n, x / i)
        }
    }

    pub open spec fn count_le(m: int, n: int, x: int) -> int
        recommends
            1 <= m <= 30000,
            1 <= n <= 30000,
            0 <= x <= m * n,
    {
        Self::count_prefix(m, n, x, m)
    }

    pub fn find_kth_number(m: i32, n: i32, k: i32) -> (result: i32)
        requires
            1 <= m <= 30000,
            1 <= n <= 30000,
            1 <= k,
            k as int <= m as int * n as int,
        ensures
            1 <= result,
            result as int <= m as int * n as int,
            Self::count_le(m as int, n as int, result as int) >= k as int,
            result == 1 || Self::count_le(m as int, n as int, (result - 1) as int) < k as int,
    {
    }
}

}
