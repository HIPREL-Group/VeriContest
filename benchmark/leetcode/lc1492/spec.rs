use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn factor_count(n: int, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else if n % i == 0 {
        factor_count(n, i - 1) + 1
    } else {
        factor_count(n, i - 1)
    }
}

impl Solution {
    pub fn kth_factor(n: i32, k: i32) -> (res: i32)
        requires
            1 <= k <= n <= 1000,
        ensures
            (res == -1 && factor_count(n as int, n as int) < k as int)
            || (1 <= res <= n && (n as int) % (res as int) == 0
                && factor_count(n as int, res as int) == k as int),
    {
    }
}

}
