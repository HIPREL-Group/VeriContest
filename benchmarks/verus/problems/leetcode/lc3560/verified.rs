use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_transport_cost(n: int, m: int, k: int) -> int
        recommends
            2 <= k <= 100_000,
            1 <= n <= 2 * k,
            1 <= m <= 2 * k,
            n <= k || m <= k,
    {
        if n <= k && m <= k {
            0
        } else if n > k {
            k * (n - k)
        } else {
            k * (m - k)
        }
    }

    pub fn min_cutting_cost(n: i32, m: i32, k: i32) -> (result: i64)
        requires
            2 <= k <= 100_000,
            1 <= n <= 2 * k,
            1 <= m <= 2 * k,
            n <= k || m <= k,
        ensures
            result as int == Self::min_transport_cost(n as int, m as int, k as int),
            result >= 0,
    {
        if n <= k && m <= k {
            0
        } else if n > k {
            let d: i64 = (n as i64) - (k as i64);
            assert(0 <= (k as int) * (d as int) <= i64::MAX as int) by (nonlinear_arith)
                requires
                    2 <= k <= 100_000,
                    n > k,
                    n <= 2 * k,
                    d == (n as i64) - (k as i64),
            {
            }
            (k as i64) * d
        } else {
            let d: i64 = (m as i64) - (k as i64);
            assert(0 <= (k as int) * (d as int) <= i64::MAX as int) by (nonlinear_arith)
                requires
                    2 <= k <= 100_000,
                    m > k,
                    m <= 2 * k,
                    d == (m as i64) - (k as i64),
            {
            }
            (k as i64) * d
        }
    }
}

}
