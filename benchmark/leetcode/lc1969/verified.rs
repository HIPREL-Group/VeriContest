use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_fundamental_div_mod, lemma_mul_mod_noop,
    lemma_small_mod,
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_commutative,
};
use vstd::arithmetic::power::{
    lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_multiplies, lemma_pow_positive,
    lemma_square_is_pow2, pow,
};
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2, lemma_pow2_pos, lemma_pow2_unfold, pow2,
};
use vstd::bits::{
    lemma_u64_low_bits_mask_is_mod, lemma_u64_shl_is_mul, lemma_u64_shr_is_div,
};

fn main() {}

verus! {

pub struct Solution;













pub open spec fn min_product_spec(p: int) -> int {
    let modulus: int = 1_000_000_007;
    let val: int = pow(2, p as nat) - 1;
    (pow(val - 1, ((val - 1) / 2) as nat) * val) % modulus
}

proof fn lemma_mul_is_zero(x: int, y: int)
    by (nonlinear_arith)
    requires
        x * y == 0,
    ensures
        x == 0 || y == 0,
{
}

proof fn lemma_div_is_zero(x: int, d: int)
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

proof fn lemma_pow_unfold(base: int, exp: nat)
    requires
        exp > 0,
    ensures
        pow(base, exp) == base * pow(base, (exp - 1) as nat) == pow(base, (exp - 1) as nat) * base,
{
    lemma_pow_adds(base, (exp - 1) as nat, 1);
    lemma_pow1(base);
    lemma_mul_is_commutative(base, pow(base, (exp - 1) as nat));
}

proof fn lemma_pow2_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow(2, a) <= pow(2, b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_pow2_le(a, (b - 1) as nat);
        lemma_pow_positive(2, (b - 1) as nat);
        lemma_pow_unfold(2, b);
    }
}

proof fn lemma_pow2_60_bound()
    ensures
        pow(2int, 60nat) == 1152921504606846976int,
{
    lemma_pow_adds(2int, 30nat, 30nat);
    lemma_pow2(30nat);
    lemma2_to64();
    assert(pow(2int, 30nat) == 1073741824int);
    assert(1073741824int * 1073741824int == 1152921504606846976int) by (nonlinear_arith);
}

impl Solution {
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
        let mut base_pow: u64 = base % modulus;
        let mut i: u64 = 0;
        let mut mut_exp: u64 = exp;
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

    pub fn min_non_zero_product(p: i32) -> (result: i32)
        requires
            1 <= p <= 60,
        ensures
            result as int == min_product_spec(p as int),
    {
        let modulus: u64 = 1_000_000_007;
        let mut val: u64 = 1;
        let mut j: i32 = 0;
        proof {
            lemma_pow0(2int);
        }
        while j < p
            invariant
                val as int == pow(2int, j as nat),
                0 <= j <= p,
                1 <= p <= 60,
            decreases p - j,
        {
            proof {
                lemma_pow_unfold(2int, (j as nat + 1));
                lemma_pow_positive(2int, j as nat);
                lemma_pow2_le((j + 1) as nat, 60nat);
                lemma_pow2_60_bound();
            }
            val = val * 2;
            j = j + 1;
        }
        proof {
            lemma_pow_positive(2int, p as nat);
            lemma_pow2_le(1nat, p as nat);
            lemma_pow1(2int);
        }
        val = val - 1;
        let power: u64 = Self::mod_pow(val - 1, val / 2, modulus);
        proof {
            lemma_pow_unfold(2int, p as nat);
            lemma_pow_positive(2int, (p - 1) as nat);
            let k = pow(2int, (p - 1) as nat);
            assert(pow(2int, p as nat) == 2 * k);
            assert(val as int == 2 * k - 1);
            assert((2 * k - 1) / 2 == k - 1) by (nonlinear_arith)
                requires
                    k >= 1,
            ;
            assert((2 * k - 2) / 2 == k - 1) by (nonlinear_arith)
                requires
                    k >= 1,
            ;
            assert(val as int / 2 == (val as int - 1) / 2);
            lemma_mul_mod_noop(
                pow((val - 1) as int, (val / 2) as nat),
                val as int,
                1_000_000_007int,
            );
            lemma_mul_inequality(power as int, (modulus - 1) as int, (val % modulus) as int);
            lemma_mul_is_commutative((modulus - 1) as int, (val % modulus) as int);
            lemma_mul_inequality((val % modulus) as int, (modulus - 1) as int, (modulus - 1) as int);
        }
        ((power * (val % modulus)) % modulus) as i32
    }
}

} 
