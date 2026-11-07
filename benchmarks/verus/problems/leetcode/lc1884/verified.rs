use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn two_egg_drop(n: i32) -> (res: i32)
        requires
            1 <= n <= 1000,
        ensures
            res >= 1,
            res * (res + 1) / 2 >= n,
            (res - 1) * res / 2 < n,
    {
        let ghost n0 = n as int;
        let mut n = n;
        let mut ans: i32 = 0;

        while n > 0
            invariant
                1 <= n0 <= 1000,
                0 <= ans <= 45,
                n == n0 - ans * (ans + 1) / 2,
                (ans - 1) * ans / 2 < n0,
            decreases 45 - ans,
        {
            proof {
                assert(ans * (ans + 1) / 2 < n0);
                assert(ans <= 44) by(nonlinear_arith)
                    requires
                        ans * (ans + 1) / 2 < 1000,
                        0 <= ans,
                ;
                assert(ans * (ans + 1) / 2 + (ans + 1)
                    == (ans + 1) * (ans + 2) / 2) by(nonlinear_arith)
                    requires
                        0 <= ans <= 44,
                ;
            }
            ans += 1;
            n -= ans;
        }

        proof {
            assert(ans * (ans + 1) / 2 >= n0);
            if ans == 0 {
                assert(false);
            }
        }

        ans
    }
}

}
