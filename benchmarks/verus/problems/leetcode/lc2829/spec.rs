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

    pub open spec fn minimum_sum_spec(n: int, k: int) -> int {
        let a = if n <= k / 2 { n } else { k / 2 };
        let b = n - a;
        Self::tri(a) + Self::sum_range(k, b)
    }

    pub fn minimum_sum(n: i32, k: i32) -> (ans: i32)
        requires
            1 <= n <= 50,
            1 <= k <= 50,
        ensures
            ans as int == Self::minimum_sum_spec(n as int, k as int),
    {
    }
}

}
