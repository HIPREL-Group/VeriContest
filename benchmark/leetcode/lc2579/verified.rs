use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn colored_until(i: nat) -> int
    recommends
        i >= 1,
{
    1 + 2 * i as int * (i as int - 1)
}

impl Solution {
    pub fn colored_cells(n: i32) -> (result: i64)
        requires
            1 <= n <= 100000,
        ensures
            result as int == colored_until(n as nat),
    {
        let mut ans: i128 = 1;
        let mut i: i128 = 1;

        while i < n as i128
            invariant
                1 <= n as int <= 100000,
                1 <= i as int <= n as int,
                ans as int == colored_until(i as nat),
            decreases n as i128 - i,
        {
            proof {
                assert(1 <= ans as int <= 20000000001) by (nonlinear_arith)
                    requires
                        ans as int == colored_until(i as nat),
                        1 <= i as int <= 100000,
                ;
                assert(4 <= 4 * i as int <= 400000);
                assert(-170141183460469231731687303715884105728
                    <= ans + 4 * i
                    < 170141183460469231731687303715884105728);
            }
            ans = ans + 4 * i;
            proof {
                assert(colored_until((i + 1) as nat) == colored_until(i as nat) + 4 * i as int) by (nonlinear_arith)
                    requires
                        1 <= i,
                ;
            }
            i = i + 1;
        }

        proof {
            assert(i as int == n as int);
            assert(ans as int == colored_until(n as nat));
            assert(1 <= n as int <= 100000);
            assert(1 <= ans as int <= 20000000001) by (nonlinear_arith)
                requires
                    ans as int == colored_until(n as nat),
                    1 <= n as int <= 100000,
            ;
            assert(-9223372036854775808 <= ans as int <= 9223372036854775807);
            assert((ans as i64) as int == ans as int);
        }

        ans as i64
    }
}

}
