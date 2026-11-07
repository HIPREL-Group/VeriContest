use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_non_zero, lemma_fundamental_div_mod, lemma_mul_mod_noop,
    lemma_small_mod,
};
use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::arithmetic::power::{
    lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_multiplies, lemma_square_is_pow2, pow,
};
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2, lemma_pow2_pos, lemma_pow2_unfold, pow2,
};
use vstd::bits::{
    lemma_u64_low_bits_mask_is_mod, lemma_u64_shl_is_mul, lemma_u64_shr_is_div, low_bits_mask,
};
use vstd::prelude::*;

fn main() {}

verus! {

pub proof fn lemma_mul_is_zero(x: int, y: int)
    by (nonlinear_arith)
    requires
        x * y == 0,
    ensures
        x == 0 || y == 0,
{
}

pub proof fn lemma_div_is_zero(x: int, d: int)
    requires
        d > 0,
    ensures
        0 <= x < d <==> x / d == 0,
{
    lemma_fundamental_div_mod(x, d);
    if 0 <= x < d {
        lemma_small_mod(x as nat, d as nat);
        lemma_mul_is_zero(d, x / d);
    }
}

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

    pub proof fn lemma_count_good_numbers_pow(n: nat)
        ensures
            n % 2 == 0 ==> Self::count_good_numbers_spec_inner(n) == pow(20, n / 2),
            n % 2 == 1 ==> Self::count_good_numbers_spec_inner(n) == 5 * pow(
                20,
                ((n - 1) / 2) as nat,
            ),
        decreases n,
    {
        lemma_pow0(20);
        reveal_with_fuel(Solution::count_good_numbers_spec_inner, 2);
        if n > 1 {
            Self::lemma_count_good_numbers_pow((n - 2) as nat);
            lemma_pow1(20);
            lemma_pow_adds(20, 1, ((n - 2) / 2) as nat);
        }
    }

    #[verifier::spinoff_prover]
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
        proof {
            assert(mut_exp == exp >> i) by (bit_vector)
                requires
                    i == 0,
                    mut_exp == exp,
            ;
            lemma_u64_shr_is_div(exp, i);
            lemma2_to64();
            lemma_pow1(base as int);
            lemma_pow0(base as int);
            lemma_small_mod(1, modulus as nat);
        }
        while mut_exp > 0
            invariant
                0 < modulus <= u32::MAX + 1,
                base_pow < modulus,
                0 <= result < modulus,
                i < 64 ==> (mut_exp == exp >> i == exp as nat / pow2(i as nat)),
                i == 64 ==> mut_exp == 0,
                0 <= i <= 64,
                result == pow(base as int, exp as nat % pow2(i as nat)) % modulus as int,
                base_pow == pow(base as int, pow2(i as nat)) % modulus as int,
            decreases mut_exp,
        {
            proof {
                assert(result == pow(base as int, exp as nat % pow2(i as nat)) % modulus as int);
                assert(exp & ((1u64 << i + 1) - 1) as u64 == (exp & (1u64 << i)) + (exp & (((1u64
                    << i) - 1) as u64))) by (bit_vector);
                assert((mut_exp & 1) << i == exp & (1u64 << i)) by (bit_vector)
                    requires
                        mut_exp == exp >> i,
                ;
                lemma2_to64();
                lemma2_to64_rest();
                if i + 1 <= 63 {
                    assert(pow2(i as nat + 1) < u64::MAX);
                    lemma_u64_shl_is_mul(1, (i + 1) as u64);
                    lemma_u64_low_bits_mask_is_mod(exp, i as nat + 1);
                } else {
                    assert(exp & ((1u64 << i + 1) - 1) as u64 == exp) by (bit_vector)
                        requires
                            i + 1 == 64,
                    ;
                    lemma_small_mod(exp as nat, pow2(64));
                }
                lemma_u64_low_bits_mask_is_mod(mut_exp, 1);
                assert(mut_exp & 1 == mut_exp % 2);
                assert(pow2(i as nat) < u64::MAX);
                assert(mut_exp & 1 <= 1);
                lemma_u64_shl_is_mul(mut_exp & 1, i);
                lemma_u64_shl_is_mul(1, i);
                lemma_u64_low_bits_mask_is_mod(exp, i as nat);
                if mut_exp % 2 == 0 {
                } else {
                    lemma_pow_adds(base as int, pow2(i as nat), exp as nat % pow2(i as nat));
                    lemma_mul_mod_noop(
                        pow(base as int, exp as nat % pow2(i as nat)),
                        pow(base as int, pow2(i as nat)),
                        modulus as int,
                    );
                }
            }
            if mut_exp % 2 != 0 {
                proof {
                    lemma_mul_inequality(base_pow as int, u32::MAX as int + 1, result as int);
                }
                result = result * base_pow % modulus;
            }
            proof {
                lemma_mul_inequality(base_pow as int, u32::MAX as int + 1, base_pow as int);
                lemma_u64_shr_is_div(mut_exp, 1);
                lemma_u64_shr_is_div(exp, i);
                if i == 63 {
                    assert(u64::MAX >> i == 1) by (bit_vector)
                        requires
                            i == 63,
                    ;
                    lemma_u64_shr_is_div(u64::MAX, i);
                    lemma_pow2_pos(i as nat);
                    lemma_div_is_ordered(exp as int, u64::MAX as int, pow2(i as nat) as int);
                } else {
                    assert(mut_exp >> 1 == exp >> (i + 1)) by (bit_vector)
                        requires
                            mut_exp == exp >> i,
                    ;
                    lemma_u64_shr_is_div(exp, (i + 1) as u64);
                }
                lemma_square_is_pow2(base_pow as int);
                lemma_mul_mod_noop(
                    pow(base as int, pow2(i as nat)),
                    pow(base as int, pow2(i as nat)),
                    modulus as int,
                );
                lemma_pow_multiplies(base as int, pow2(i as nat), 2);
                lemma_square_is_pow2(pow(base as int, pow2(i as nat)));
                lemma_pow2_unfold(i as nat + 1);
            }
            base_pow = base_pow * base_pow % modulus;
            mut_exp >>= 1;
            i += 1;
        }
        proof {
            assert(result == pow(base as int, exp as nat % pow2(i as nat)) % modulus as int);
            if i == 64 {
                lemma2_to64();
            } else {
                lemma_pow2_pos(i as nat);
                lemma_div_is_zero(exp as int, pow2(i as nat) as int);
            }
            lemma_small_mod(exp as nat, pow2(i as nat));
        }
        result
    }

    pub fn count_good_numbers(n: i64) -> (res: i32)
        requires
            1 <= n <= pow(10, 15),
        ensures
            res == Self::count_good_numbers_spec(n as nat) as i32,
    {
        proof {
            Self::lemma_count_good_numbers_pow(n as nat);
        }
        ((Self::mod_pow(4 * 5, n as u64 / 2, Self::M) * if n % 2 == 1 {
            5
        } else {
            1
        }) % Self::M) as i32
    }
}

} 
