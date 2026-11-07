use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs_i(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

pub open spec fn spec_abs_diff(c1: int, c2: int) -> int {
    if c1 >= c2 {
        c1 - c2
    } else {
        c2 - c1
    }
}

pub open spec fn spec_feasible(c1: int, c2: int, n: int) -> bool {
    c1 >= 0 && c2 >= 0 && c1 + 2 * c2 == n
}

pub open spec fn spec_k_feasible(k: int, n: int) -> bool {
    0 <= k && 2 * k <= n
}

pub open spec fn spec_abs_triple(n: int, k: int) -> int {
    spec_abs_i(n - 3 * k)
}

pub open spec fn spec_k_lo(n: int) -> int {
    n / 3
}

pub open spec fn spec_k_hi(n: int) -> int {
    (n + 2) / 3
}

impl Solution {
    pub fn polycarp_coins(n: i64) -> (res: (i64, i64))
        requires
            1 <= n <= 1_000_000_000,
        ensures
            spec_feasible(res.0 as int, res.1 as int, n as int),
            forall|c1p: int, c2p: int|
                spec_feasible(c1p, c2p, n as int) ==> #[trigger] spec_abs_diff(res.0 as int, res.1 as int)
                    <= spec_abs_diff(c1p, c2p),
            exists|c1e: int, c2e: int|
                c1e == res.0 as int && c2e == res.1 as int && #[trigger] spec_feasible(c1e, c2e, n as int),
    {
        let k_lo = n / 3;
        let d_lo = n - 3 * k_lo;
        let k_hi = (n + 2) / 3;
        let c2 = if k_hi != k_lo && 2 * k_hi <= n {
            let t = n - 3 * k_hi;
            let d_hi = if t < 0 {
                -t
            } else {
                t
            };
            if d_hi < d_lo {
                k_hi
            } else {
                k_lo
            }
        } else {
            k_lo
        };
        let c1 = n - 2 * c2;
        proof {
            assert(exists|c1e: int, c2e: int|
                c1e == c1 as int && c2e == c2 as int && spec_feasible(c1e, c2e, n as int)) by {
                assert(spec_feasible(c1 as int, c2 as int, n as int));
            };
        }
        (c1, c2)
    }
}

}
