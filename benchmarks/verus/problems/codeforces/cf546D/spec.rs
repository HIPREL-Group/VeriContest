use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn divides(n: int, d: int) -> bool {
    1 <= d && n % d == 0
}

pub open spec fn has_factor_below(n: int, bound: int) -> bool
    recommends
        2 <= bound,
{
    exists|d: int| 2 <= d < bound && #[trigger] divides(n, d)
}

pub open spec fn least_divisor(n: int, d: int) -> bool {
    &&& 2 <= d <= n
    &&& divides(n, d)
    &&& forall|e: int| 2 <= e < d && #[trigger] divides(n, e) ==> false
}

pub open spec fn is_prime(n: int) -> bool {
    2 <= n && forall|d: int| 2 <= d < n && #[trigger] divides(n, d) ==> false
}

pub open spec fn smallest_divisor_from(n: int, d: int) -> int
    recommends
        2 <= d <= n,
    decreases n - d,
{
    if d >= n {
        n
    } else if n % d == 0 {
        d
    } else {
        smallest_divisor_from(n, d + 1)
    }
}

pub open spec fn smallest_prime_divisor(n: int) -> int
    recommends
        2 <= n,
{
    smallest_divisor_from(n, 2)
}

pub open spec fn omega(n: int) -> int
    recommends
        1 <= n,
    decreases n,
{
    if n <= 1 {
        0
    } else {
        let q = n / smallest_prime_divisor(n);
        if q >= n {
            1
        } else if q <= 1 {
            1
        } else {
            1 + omega(q)
        }
    }
}

pub open spec fn omega_prefix(n: int) -> int
    recommends
        0 <= n,
    decreases n,
{
    if n <= 1 {
        0
    } else {
        omega_prefix(n - 1) + omega(n)
    }
}

pub open spec fn omega_interval_sum(lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi,
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        omega_interval_sum(lo, hi - 1) + omega(hi)
    }
}

impl Solution {
    pub fn max_scores_for_games(queries: Vec<(i32, i32)>) -> (res: Vec<u64>)
        requires
            1 <= queries.len() <= 1_000_000,
            forall|k: int|
                0 <= k < queries.len() ==> {
                    let (a, b) = #[trigger] queries[k];
                    1 <= b <= a <= 5_000_000
                },
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k < res.len() ==> #[trigger] res[k] as int == omega_interval_sum(
                    queries[k].1 as int,
                    queries[k].0 as int,
                ),
    {
    }
}

}
