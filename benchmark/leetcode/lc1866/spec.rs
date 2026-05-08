use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn stirling_mod(n: int, k: int) -> int
    decreases n
{
    if k < 0 || k > n || n < 0 {
        0
    } else if n == k {
        1
    } else if k == 0 {
        0
    } else {
        (stirling_mod(n - 1, k - 1) + ((n - 1) * stirling_mod(n - 1, k)) % 1_000_000_007) % 1_000_000_007
    }
}

impl Solution {
    pub fn rearrange_sticks(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            1 <= k <= n,
        ensures
            result == stirling_mod(n as int, k as int) as i32,
    {
    }
}

}

