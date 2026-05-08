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
    fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64 {
        if modulus == 1 {
            return 0
        }
        let mut result = 1;
        let mut base_pow = base % modulus;
        let mut i: u64 = 0;
        let mut mut_exp = exp;
        while mut_exp > 0 {
            if mut_exp % 2 != 0 {
                result = result * base_pow % modulus;
            }
            base_pow = base_pow * base_pow % modulus;
            mut_exp >>= 1;
            i += 1;
        }
        result
    }

    pub fn min_quiz_score(n: i64, m: i64, k: i64) -> (result: i64)
        requires
            2 <= k <= n <= 1_000_000_000,
            0 <= m <= n,
        ensures
            result as int == spec_quiz_answer(n as int, m as int, k as int),
    {
        let wrong = n - m;
        let lhs = (wrong as i128 + 1) * (k as i128 - 1);
        if lhs >= m as i128 {
            m % MOD
        } else {
            let consecutive = m - wrong * (k - 1);
            let t = consecutive / k;
            let pow2t = Self::mod_pow(2, t as u64, MOD as u64) as i64;
            let x = (pow2t - 1) * 2;
            let term = x * k + m - t * k;
            let mut rem = term % MOD;
            if rem < 0 {
                rem = rem + MOD;
            }
            rem
        }
    }
}

}
