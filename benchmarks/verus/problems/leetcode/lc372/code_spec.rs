use vstd::arithmetic::power::pow;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const M: u64 = 1337;

    pub open spec fn digits_to_nat(digits: Seq<i32>) -> nat
        recommends
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        decreases digits.len(),
    {
        if digits.len() == 0 {
            0
        } else {
            let tail = digits.last() as nat;
            let remainder = digits.drop_last();
            10 * Self::digits_to_nat(remainder) + tail
        }
    }

    pub open spec fn super_pow_spec(a: int, b: Seq<i32>) -> int
        recommends
            forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] <= 9,
    {
        pow(a, Self::digits_to_nat(b)) % Self::M as int
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

    pub fn super_pow(a: i32, b: Vec<i32>) -> (res: i32)
        requires
            1 <= a <= i32::MAX,
            1 <= b.len() <= 2000,
            forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] <= 9,
            b[0] > 0,
        ensures
            res == Self::super_pow_spec(a as int, b@) as i32,
    {
        let mut result: u64 = 1;
        let mut base_pow = a as u64 % Self::M;
        let mut i = 0;
        while i < b.len()
        {
            let mp = Self::mod_pow(base_pow, b[b.len() - i - 1] as u64, Self::M);
            result = result * mp % Self::M;
            base_pow = Self::mod_pow(base_pow, 10, Self::M);
            i += 1;
        }
        result as i32
    }
}

} 
