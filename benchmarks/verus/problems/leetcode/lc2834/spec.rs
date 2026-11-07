use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tri(x: int) -> int {
        x * (x + 1) / 2
    }

    pub open spec fn sum_range(start: int, count: int) -> int {
        count * (2 * start + count - 1) / 2
    }

    pub open spec fn minimum_raw(n: int, target: int) -> int {
        let a = if n <= target / 2 { n } else { target / 2 };
        let b = n - a;
        Self::tri(a) + Self::sum_range(target, b)
    }

    pub fn minimum_possible_sum(n: i32, target: i32) -> (ans: i32)
        requires
            1 <= n <= 1000000000,
            1 <= target <= 1000000000,
        ensures
            ans as int == Self::minimum_raw(n as int, target as int) % 1000000007,
    {
    }
}

}
