use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub const MOD: i64 = 1000000009;

pub open spec fn spec_pos_mod(x: int, m: int) -> int {
    (x % m + m) % m
}

pub open spec fn spec_quiz_answer(n: int, m: int, k: int) -> int {
    let wrong = n - m;
    let mi = MOD as int;
    if (wrong + 1) * (k - 1) >= m {
        spec_pos_mod(m, mi)
    } else {
        let consecutive = m - wrong * (k - 1);
        let t = consecutive / k;
        let p2 = pow(2, t as nat) % mi;
        let term = (p2 - 1) * 2 * k + m - t * k;
        spec_pos_mod(term, mi)
    }
}

pub struct Solution;

impl Solution {
    pub fn min_quiz_score(n: i64, m: i64, k: i64) -> (result: i64)
        requires
            2 <= k <= n <= 1_000_000_000,
            0 <= m <= n,
        ensures
            result as int == spec_quiz_answer(n as int, m as int, k as int),
    {
    }
}

}
