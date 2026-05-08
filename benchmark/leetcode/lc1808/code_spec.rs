use vstd::prelude::*;
use vstd::arithmetic::power::pow;

fn main() {}

verus! {

pub struct Solution;

#[verifier::spinoff_prover]
fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64
    requires
        0 < modulus <= u32::MAX + 1,
    returns
        (pow(base as int, exp as nat) % modulus as int) as u64,
{
    if modulus == 1 {
        return 0;
    }
    let mut result: u64 = 1;
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

impl Solution {
    pub open spec fn partition_sum(parts: Seq<int>, hi: int) -> int
        decreases hi,
    {
        if hi <= 0 {
            0
        } else {
            Self::partition_sum(parts, hi - 1) + parts[hi - 1]
        }
    }

    pub open spec fn partition_product(parts: Seq<int>, hi: int) -> int
        decreases hi,
    {
        if hi <= 0 {
            1
        } else {
            Self::partition_product(parts, hi - 1) * parts[hi - 1]
        }
    }

    pub fn max_nice_divisors(prime_factors: i32) -> (res: i32)
        requires
            1 <= prime_factors <= 1_000_000_000,
        ensures
            0 <= res,
            exists |parts: Seq<int>|
                #![trigger Self::partition_product(parts, parts.len() as int)]
                parts.len() > 0
                && (forall |i: int| 0 <= i < parts.len() ==> parts[i] >= 1)
                && Self::partition_sum(parts, parts.len() as int) == prime_factors as int
                && Self::partition_product(parts, parts.len() as int) % 1_000_000_007 == res as int
                && (forall |other: Seq<int>|
                    #![trigger Self::partition_product(other, other.len() as int)]
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == prime_factors as int
                    ==> Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(parts, parts.len() as int)),
    {
        let modulus: u64 = 1_000_000_007;
        if prime_factors <= 3 {
            return prime_factors;
        }
        let pf = prime_factors as u64;
        let remainder = pf % 3;
        if remainder == 0 {
            let p = mod_pow(3, pf / 3, modulus);
            p as i32
        } else if remainder == 1 {
            let exp = (pf - 4) / 3;
            let p = mod_pow(3, exp, modulus);
            (4 * p % modulus) as i32
        } else {
            let exp = pf / 3;
            let p = mod_pow(3, exp, modulus);
            (2 * p % modulus) as i32
        }
    }
}

} 
