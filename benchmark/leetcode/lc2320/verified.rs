use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn modv(x: int) -> int {
        x % 1000000007
    }

    pub open spec fn one_side_ways(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            1
        } else if n == 1 {
            2
        } else {
            Self::modv(Self::one_side_ways(n - 1) + Self::one_side_ways(n - 2))
        }
    }

    pub fn count_house_placements(n: i32) -> (ans: i32)
        requires
            1 <= n <= 10000,
        ensures
            ans as int == Self::modv(Self::one_side_ways(n as int) * Self::one_side_ways(n as int)),
    {
        let m: i64 = 1_000_000_007;
        let mut a: i64 = 1;
        let mut b: i64 = 2;
        let mut i: i32 = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                1 <= n <= 10000,
                m == 1_000_000_007,
                0 <= a < m,
                0 <= b < m,
                a as int == Self::one_side_ways((i - 2) as int),
                b as int == Self::one_side_ways((i - 1) as int),
            decreases n - i + 1,
        {
            let c = (a + b) % m;
            proof {
                assert(0 <= a + b < 2 * 1_000_000_007) by (nonlinear_arith)
                    requires 0 <= a < m, 0 <= b < m, m == 1_000_000_007
                {
                }
                assert(c as int == Self::modv(a as int + b as int)) by (nonlinear_arith)
                    requires
                        c as int == ((a as int + b as int) % 1000000007int),
                        m == 1_000_000_007,
                        0 <= a + b,
                {
                }
            }
            a = b;
            b = c;
            proof {
                assert(i < 2147483647) by (nonlinear_arith)
                    requires i <= n, n <= 10000
                {
                }
            }
            i = i + 1;
        }
        let one = if n == 1 { 2 } else { b };
        proof {
            if n == 1 {
                assert(one as int == Self::one_side_ways(n as int));
            } else {
                assert(i == n + 1);
                assert(one == b);
                assert(one as int == Self::one_side_ways(n as int));
            }
            assert(0 <= one < m);
            assert(0 <= one * one < m * m) by (nonlinear_arith)
                requires 0 <= one < m
            {
            }
            assert(((one as int) * (one as int)) % 1000000007int >= 0) by (nonlinear_arith)
                requires m > 0, 0 <= one
            {
            }
            assert(((one as int) * (one as int)) % 1000000007int == Self::modv((one as int) * (one as int))) by (nonlinear_arith)
                requires
                    m == 1_000_000_007,
                    0 <= one * one,
            {
            }
        }
        ((one * one) % m) as i32
    }
}

}
