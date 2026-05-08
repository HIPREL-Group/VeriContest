use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub open spec fn alice_wins(x: int, y: int) -> bool {
        (x + y) % 2 == 1
    }

    pub fn flower_game(n: i32, m: i32) -> (result: i64)
        requires
            1 <= n <= 100000,
            1 <= m <= 100000,
        ensures
            result == (((n as u128) * (m as u128)) / 2) as i64,
            forall |x: int, y: int| 1 <= x <= n && 1 <= y <= m ==> (#[trigger] Self::alice_wins(x, y) <==> (x % 2 != y % 2)),
    {
        let nu = n as u128;
        let mu = m as u128;
        proof {
            assert(1 <= nu <= 100000);
            assert(1 <= mu <= 100000);
            assert(nu * mu <= 10000000000) by (nonlinear_arith)
                requires
                    nu <= 100000,
                    mu <= 100000,
            {}
            assert((nu * mu) / 2 <= 5000000000) by (nonlinear_arith)
                requires
                    nu * mu <= 10000000000,
            {}
            assert((nu * mu) / 2 <= 9223372036854775807) by (nonlinear_arith)
                requires
                    (nu * mu) / 2 <= 5000000000,
            {}
        }
        (((n as u128) * (m as u128)) / 2) as i64
    }
}
}
