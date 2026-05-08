use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_divisors_up_to(n: int, k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else {
        count_divisors_up_to(n, k - 1) + if n % k == 0 { 1int } else { 0int }
    }
}

impl Solution {
    pub fn is_three(n: i32) -> (res: bool)
        requires
            1 <= n <= 10_000,
        ensures
            res == (count_divisors_up_to(n as int, n as int) == 3),
    {
        let mut count: i32 = 0;
        let mut i: i32 = 1;
        while i <= n
            invariant
                1 <= n <= 10_000,
                1 <= i <= n + 1,
                0 <= count <= i - 1,
                count as int == count_divisors_up_to(n as int, (i - 1) as int),
            decreases n - i + 1,
        {
            if n % i == 0 {
                count = count + 1;
            }
            i = i + 1;
        }
        count == 3
    }
}

}
