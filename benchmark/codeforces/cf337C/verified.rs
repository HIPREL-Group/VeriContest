use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_non_zero, lemma_fundamental_div_mod, lemma_mul_mod_noop,
    lemma_mul_mod_noop_right, lemma_small_mod,
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add,
};
use vstd::arithmetic::power::{
    lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_multiplies, lemma_pow_positive,
    lemma_square_is_pow2, pow,
};
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2, lemma_pow2_pos, lemma_pow2_unfold, pow2,
};
use vstd::bits::{
    lemma_u64_low_bits_mask_is_mod, lemma_u64_shl_is_mul, lemma_u64_shr_is_div, low_bits_mask,
};
use vstd::calc;
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

pub proof fn lemma_pow_unfold(base: int, exp: nat)
    requires
        exp > 0,
    ensures
        pow(base, exp) == base * pow(base, (exp - 1) as nat) == pow(base, (exp - 1) as nat) * base,
{
    lemma_pow_adds(base, (exp - 1) as nat, 1);
    lemma_pow1(base);
    lemma_mul_is_commutative(base, pow(base, (exp - 1) as nat));
}

pub proof fn lemma_mod_pow_base(base: int, exp: nat, modulus: int)
    requires
        modulus > 0,
    ensures
        pow(base, exp) % modulus == pow(base % modulus, exp) % modulus,
    decreases exp,
{
    if exp == 0 {
        lemma_pow0(base);
        lemma_pow0(base % modulus);
    } else {
        calc! {
            (==)
            pow(base, exp) % modulus; { lemma_pow_unfold(base, exp) }
            (base * pow(base, (exp - 1) as nat)) % modulus; {
                lemma_mul_mod_noop(base, pow(base, (exp - 1) as nat), modulus)
            }
            ((base % modulus) * (pow(base, (exp - 1) as nat) % modulus)) % modulus; {
                lemma_mod_pow_base(base, (exp - 1) as nat, modulus)
            }
            ((base % modulus) * (pow(base % modulus, (exp - 1) as nat) % modulus)) % modulus; {
                lemma_mul_mod_noop_right(
                    base % modulus,
                    pow(base % modulus, (exp - 1) as nat),
                    modulus,
                )
            }
            ((base % modulus) * pow(base % modulus, (exp - 1) as nat)) % modulus; {
                lemma_pow_unfold(base % modulus, exp)
            }
            pow(base % modulus, exp) % modulus;
        }
    }
}

pub const MOD: i64 = 1000000009;

proof fn lemma_quot_ge_one(a: int, b: int)
    requires
        b > 0,
        a >= b,
    ensures
        a / b >= 1,
{
    assert(a / b >= 1) by (nonlinear_arith)
        requires
            b > 0,
            a >= b,
    {
    }
}

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
    #[verifier::spinoff_prover]
    fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64
        requires
            0 < modulus <= u32::MAX + 1,
        returns
            (pow(base as int, exp as nat) % modulus as int) as u64,
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

    #[verifier::spinoff_prover]
    pub fn min_quiz_score(n: i64, m: i64, k: i64) -> (result: i64)
        requires
            2 <= k <= n <= 1_000_000_000,
            0 <= m <= n,
        ensures
            result as int == spec_quiz_answer(n as int, m as int, k as int),
    {
        proof {
            assert(0 <= n <= 1_000_000_000);
            assert(0 <= m <= n);
            assert(2 <= k <= n);
            assert(2 <= k <= 1_000_000_000);
        }
        let wrong = n - m;
        proof {
            assert(0 <= wrong <= 1_000_000_000);
            assert((wrong as int + 1) * ((k as int) - 1) <= 1000000000000000000) by (nonlinear_arith)
                requires
                    0 <= wrong <= 1_000_000_000,
                    2 <= k <= 1_000_000_000,
            {
            }
            assert((wrong as i128 + 1) * (k as i128 - 1) <= 1000000000000000000i128) by (nonlinear_arith)
                requires
                    0 <= wrong <= 1_000_000_000,
                    2 <= k <= 1_000_000_000,
            {
            }
        }
        let lhs = (wrong as i128 + 1) * (k as i128 - 1);
        if lhs >= m as i128 {
            proof {
                lemma_fundamental_div_mod(m as int, MOD as int);
                assert(spec_quiz_answer(n as int, m as int, k as int) == spec_pos_mod(m as int, MOD as int));
                assert((m % MOD) as int == spec_pos_mod(m as int, MOD as int));
            }
            m % MOD
        } else {
            proof {
                assert((wrong as int) * ((k as int) - 1) <= 1000000000000000000) by (nonlinear_arith)
                    requires
                        0 <= wrong <= 1_000_000_000,
                        2 <= k <= 1_000_000_000,
                {
                }
            }
            let consecutive = m - wrong * (k - 1);
            proof {
                assert(lhs < m as i128);
                assert((wrong as int + 1) * ((k as int) - 1) == lhs as int);
                assert((lhs as int) < (m as int));
                assert((wrong as int + 1) * ((k as int) - 1) < m as int);
                assert((m as int) - (wrong as int) * ((k as int) - 1) >= (k as int)) by (nonlinear_arith)
                    requires
                        (wrong as int + 1) * ((k as int) - 1) < m as int,
                        2 <= k <= 1_000_000_000,
                        0 <= wrong <= 1_000_000_000,
                {
                }
                assert((consecutive as int) == (m as int) - (wrong as int) * ((k as int) - 1));
                assert((consecutive as int) >= (k as int));
                assert(consecutive >= k);
            }
            let t = consecutive / k;
            proof {
                lemma_quot_ge_one(consecutive as int, k as int);
                assert(t as int == (consecutive as int) / (k as int));
            }
            let pow2t = Self::mod_pow(2, t as u64, MOD as u64) as i64;
            proof {
                assert(1 <= t <= 1_000_000_000);
                assert(0 <= pow2t < MOD);
            }
            proof {
                assert((pow2t as int - 1) * 2 <= 2500000000) by (nonlinear_arith)
                    requires
                        0 <= pow2t < MOD,
                {
                }
            }
            let x = (pow2t - 1) * 2;
            proof {
                assert((pow2t as int - 1) * 2 * (k as int) <= 5000000000000000000) by (nonlinear_arith)
                    requires
                        0 <= pow2t < MOD,
                        2 <= k <= 1_000_000_000,
                {
                }
                assert((t as int) * (k as int) <= 1000000000000000000) by (nonlinear_arith)
                    requires
                        1 <= t <= 1_000_000_000,
                        2 <= k <= 1_000_000_000,
                {
                }
                assert(
                    ((pow2t as int - 1) * 2 * (k as int) + (m as int) - (t as int) * (k as int) <= 6000000000000000000)
                    && ((pow2t as int - 1) * 2 * (k as int) + (m as int) - (t as int) * (k as int) >= -6000000000000000000)
                ) by (nonlinear_arith)
                    requires
                        0 <= pow2t < MOD,
                        0 <= m <= 1_000_000_000,
                        2 <= k <= 1_000_000_000,
                        1 <= t <= 1_000_000_000,
                {
                }
            }
            let term = x * k + m - t * k;
            let mut rem = term % MOD;
            if rem < 0 {
                rem = rem + MOD;
            }
            proof {
                assert(rem as int == spec_quiz_answer(n as int, m as int, k as int));
            }
            rem
        }
    }
}

}

