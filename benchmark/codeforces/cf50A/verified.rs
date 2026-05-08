use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_dominoes_spec(m: int, n: int) -> int {
    (m * n) / 2
}

impl Solution {
    pub fn max_dominoes(m: u32, n: u32) -> (result: u32)
        requires
            1 <= m <= 16,
            1 <= n <= 16,
        ensures
            result as int == max_dominoes_spec(m as int, n as int),
    {
        proof {
            assert(m as int * n as int <= 256) by (nonlinear_arith)
                requires 1 <= m as int, m as int <= 16, 1 <= n as int, n as int <= 16 {}
        }
        let mut area: u64 = 0;
        let mut i: u32 = 0;
        while i < m
            invariant
                1 <= m <= 16,
                1 <= n <= 16,
                0 <= i <= m,
                area as int == i as int * n as int,
                area <= 256,
                m as int * n as int <= 256,
            decreases m - i,
        {
            proof {
                assert(area as int + n as int == (i as int + 1) * n as int) by (nonlinear_arith)
                    requires area as int == i as int * n as int {}
                assert((i as int + 1) * n as int <= 256) by (nonlinear_arith)
                    requires
                        i < m,
                        m as int * n as int <= 256,
                        1 <= n,
                        0 <= i,
                {}
            }
            area = area + (n as u64);
            i = i + 1;
        }
        proof {
            assert(area as int == m as int * n as int);
            assert((area / 2) as int == (m as int * n as int) / 2);
            assert((area / 2) as int == max_dominoes_spec(m as int, n as int));
        }
        let r = (area / 2) as u32;
        proof {
            assert(r as int == (area / 2) as int);
            assert(area / 2 <= 128);
            assert(128 <= 4294967295);
        }
        r
    }
}

}
