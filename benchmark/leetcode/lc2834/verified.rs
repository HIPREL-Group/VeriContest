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
        let m: i64 = 1_000_000_007;
        let a: i64 = if (n as i64) <= (target as i64) / 2 { n as i64 } else { (target as i64) / 2 };
        let b: i64 = n as i64 - a;
        proof {
            assert(0 <= a <= 1000000000);
            assert(0 <= b <= 1000000000);
            assert(0 <= a * (a + 1) <= 1000000001000000000) by (nonlinear_arith)
                requires 0 <= a <= 1000000000
            {
            }
            assert(0 <= b * (2 * target as i64 + b - 1) <= 2999999999000000000) by (nonlinear_arith)
                requires
                    0 <= b <= 1000000000,
                    1 <= target as int <= 1000000000,
            {
            }
        }
        let left: i64 = a * (a + 1) / 2;
        let right: i64 = b * (2 * target as i64 + b - 1) / 2;
        ((left + right) % m) as i32
    }
}

}
