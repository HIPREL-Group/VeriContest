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
        let mut count: i32 = 0;
        let mut i: i32 = 1;
        while i <= n
            invariant
                1 <= k <= n <= 1000,
                1 <= i <= n + 1,
                0 <= count < k,
                count as int == factor_count(n as int, (i - 1) as int),
            decreases n - i + 1,
        {
            if n % i == 0 {
                count = count + 1;
                if count == k {
                    return i;
                }
            }
            i = i + 1;
        }
        -1
    }
}

}
