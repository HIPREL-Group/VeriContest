use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_count(n: int) -> int
        decreases n,
    {
        if n <= 1 {
            1
        } else {
            Self::valid_count(n - 1) * n * (2 * n - 1)
        }
    }

    pub fn count_orders(n: i32) -> (result: i32)
        requires
            1 <= n <= 500,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Self::valid_count(n as int) % 1_000_000_007,
    {
        let m: i64 = 1_000_000_007;
        let mut count: i64 = 1;
        let mut i: i64 = 2;
        while i <= n as i64 {
            let factor: i64 = (2 * i - 1) * i;
            count = (count * factor) % m;
            i += 1;
        }
        count as i32
    }
}

}
