use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_non_zero, lemma_fundamental_div_mod, lemma_mul_mod_noop,
    lemma_mul_mod_noop_right, lemma_small_mod, lemma_div_decreases, lemma_mod_equivalence, lemma_mod_is_zero, lemma_mod_multiples_vanish
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add, lemma_mul_by_zero_is_zero, lemma_mul_is_distributive_add_other_way
};
use vstd::arithmetic::power::{
    lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_multiplies, lemma_pow_positive,
    lemma_square_is_pow2, pow,
};
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2, lemma_pow2_pos, lemma_pow2_unfold, pow2,
};
use vstd::arithmetic::logarithm::{
    lemma_log0, log, lemma_log_s, lemma_log_nonnegative
};
use vstd::bits::{
    lemma_u64_low_bits_mask_is_mod, lemma_u64_shl_is_mul, lemma_u64_shr_is_div, low_bits_mask,
};
use vstd::calc;
use vstd::prelude::*;

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

pub proof fn lemma_pow_log_upperbound(b: int, n: int)
    requires
        n > 0,
        b > 1,
    ensures
        pow(b, log(b, n) as nat) <= n,
    decreases n,
{
    if n < b {
        lemma_log0(b, n);
        lemma_pow0(b);
        lemma_pow1(b);
    } else {
        let k = log(b, n) as nat;
        let k_prev = log(b, n / b) as nat;
        lemma_div_decreases(n, b);
        lemma_div_non_zero(n, b);
        lemma_pow_log_upperbound(b, n / b);

        lemma_log_s(b, n);
        lemma_log_nonnegative(b, n / b);
        lemma_pow_adds(b, k_prev, 1);
        lemma_pow1(b);
        lemma_fundamental_div_mod(n, b);
        lemma_mul_inequality(pow(b, k_prev), n / b, b);
    }
}

pub proof fn lemma_mod_congruent(x: int, y: int, m: int)
    requires
        x % m == y % m,
        0 <= x <= y,
        m > 0,
    ensures
        exists|n: nat| y == #[trigger] (n * m) + x,
    decreases y,
{
    lemma_mod_equivalence(y, x, m);
    let diff = y - x;
    if diff == 0 {
        lemma_mul_by_zero_is_zero(m);
    } else {
        lemma_mod_is_zero(diff as nat, m as nat);
        if diff == m {
            assert(y == 1 * m + x);
        } else {
            lemma_mod_multiples_vanish(-1, y, m);
            lemma_mod_congruent(x, y - m, m);
            let last_n = choose|n: nat| (y - m) == #[trigger] (n * m) + x;
            lemma_mul_is_distributive_add_other_way(m, last_n as int, 1);
        }
    }
}

#[verifier::spinoff_prover]
pub fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64
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

pub assume_specification[ i32::pow ](base: i32, exp: u32) -> (res: i32)
    requires
        pow(base as int, exp as nat) <= i32::MAX,
    ensures
        res == pow(base as int, exp as nat),
;

pub assume_specification[ i32::ilog ](n: i32, base: i32) -> (res: u32)
    requires
        base >= 2,
        n > 0,
    ensures
        res == log(base as int, n as int),
;

pub proof fn even_minus_two_is_even(n: nat)
    requires n >= 2, n % 2 == 0,
    ensures (n - 2) % 2 == 0,
{
}

} // verus!
