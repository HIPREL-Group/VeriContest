use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const M: u64 = 1_000_000_007;

    pub open spec fn count_good_numbers_spec_inner(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else if n % 2 == 1 {
            5 * Self::count_good_numbers_spec_inner((n - 1) as nat)
        } else {
            4 * Self::count_good_numbers_spec_inner((n - 1) as nat)
        }
    }

    pub open spec fn count_good_numbers_spec(n: nat) -> nat {
        Self::count_good_numbers_spec_inner(n) % Self::M as nat
    }

    fn mod_pow(base: u64, exp: u64, modulus: u64) -> (res: u64)
        requires
            0 < modulus <= u32::MAX + 1,
        ensures
            res == (pow(base as int, exp as nat) % modulus as int) as u64,
    {
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

    pub fn count_good_numbers(n: i64) -> (res: i32)
        requires
            1 <= n <= pow(10, 15),
        ensures
            res == Self::count_good_numbers_spec(n as nat) as i32,
    {
        ((Self::mod_pow(4 * 5, n as u64 / 2, Self::M) * if n % 2 == 1 {
            5
        } else {
            1
        }) % Self::M) as i32
    }
}

} 
