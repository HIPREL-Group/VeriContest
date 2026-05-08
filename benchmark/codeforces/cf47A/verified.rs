use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_triangular(n: u32) -> (result: bool)
        requires
            1 <= n <= 500,
        ensures
            result == (exists|k: int| 1 <= k <= n && #[trigger] (k * (k + 1) / 2) == n as int),
    {
        let mut k: u32 = 1;
        while k <= n
            invariant
                1 <= k <= n + 1,
                1 <= n <= 500,
                forall|kk: int| 1 <= kk < k ==> #[trigger] (kk * (kk + 1) / 2) != n as int,
            decreases (n + 1) - k,
        {
            assert((k * (k + 1) / 2) <= 500 * 501 / 2) by (nonlinear_arith) requires k <= 500u32;
            if k * (k + 1) / 2 == n {
                assert(k as int * (k as int + 1) / 2 == n as int);
                return true;
            }
            k = k + 1;
        }
        proof {
            assert(k == n + 1);
            assert(forall|kk: int| 1 <= kk <= n ==> #[trigger] (kk * (kk + 1) / 2) != n as int);
        }
        false
    }
}

}
