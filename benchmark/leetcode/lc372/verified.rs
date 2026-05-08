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
use vstd::seq::Seq;
use vstd::seq_lib::lemma_seq_skip_nothing;

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

    pub proof fn lemma_digits_empty_yield_zero()
        ensures
            Self::digits_to_nat(Seq::empty()) == 0,
    {
    }

    pub proof fn lemma_one_more_digit(digits: Seq<i32>)
        requires
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
            digits.len() >= 1,
        ensures
            Self::digits_to_nat(digits) == digits.first() * pow(10, (digits.len() - 1) as nat)
                + Self::digits_to_nat(digits.drop_first()),
        decreases digits.len(),
    {
        if digits.len() == 1 {
            Self::lemma_digits_empty_yield_zero();
            assert(digits.drop_last() == Seq::<i32>::empty());
            lemma_pow0(10);
        } else {
            let remainder = digits.drop_last();
            calc! {
                (==)
                Self::digits_to_nat(digits) as int; {}
                10 * Self::digits_to_nat(remainder) + digits.last(); {
                    Self::lemma_one_more_digit(remainder)
                }
                10 * (remainder.first() * pow(10, (remainder.len() - 1) as nat)
                    + Self::digits_to_nat(remainder.drop_first())) + digits.last(); {
                    lemma_mul_is_distributive_add(
                        10,
                        remainder.first() * pow(10, (remainder.len() - 1) as nat),
                        Self::digits_to_nat(remainder.drop_first()) as int,
                    )
                }
                10 * (remainder.first() * pow(10, (remainder.len() - 1) as nat)) + 10
                    * Self::digits_to_nat(remainder.drop_first()) + digits.last(); {
                    lemma_mul_is_associative(
                        10,
                        remainder.first() as int,
                        pow(10, (remainder.len() - 1) as nat),
                    );
                    assert(digits.drop_first().drop_last() == remainder.drop_first())
                }
                10 * remainder.first() * pow(10, (remainder.len() - 1) as nat)
                    + Self::digits_to_nat(digits.drop_first()); {
                    lemma_mul_is_commutative(10, remainder.first() as int);
                    lemma_mul_is_associative(
                        remainder.first() as int,
                        10,
                        pow(10, (remainder.len() - 1) as nat),
                    )
                }
                digits.first() * (10 * pow(10, (digits.len() - 2) as nat)) + Self::digits_to_nat(
                    digits.drop_first(),
                ); { lemma_pow_unfold(10, (digits.len() - 1) as nat) }
                digits.first() * pow(10, (digits.len() - 1) as nat) + Self::digits_to_nat(
                    digits.drop_first(),
                );
            }
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
        proof {
            lemma_pow0(10);
            lemma_pow0(a as int);
            lemma_pow1(a as int);
        }
        while i < b.len()
            invariant
                base_pow == pow(a as int, pow(10, i as nat) as nat) % Self::M as int,
                forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] <= 9,
                result == Self::super_pow_spec(a as int, b@.skip(b.len() - i)),
                result < Self::M,
                0 <= i <= b.len(),
            decreases b.len() - i,
        {
            let mp = Self::mod_pow(base_pow, b[b.len() - i - 1] as u64, Self::M);
            proof {
                assert(result * mp < Self::M * Self::M) by (nonlinear_arith)
                    requires
                        result < Self::M,
                        mp < Self::M,
                ;
                lemma_pow_multiplies(a as int, pow(10, i as nat) as nat, 10);
                lemma_pow_unfold(10, i as nat + 1);
                lemma_pow_positive(10, i as nat);
                lemma_mod_pow_base(pow(a as int, pow(10, i as nat) as nat), 10, Self::M as int);
                let b_ext = b@.skip(b.len()-i-1);
                let a_i = a as int;
                let m_i = Self::M as int;
                calc! {
                    (==)
                    pow(a_i, Self::digits_to_nat(b_ext)) % m_i; {
                        Self::lemma_one_more_digit(b_ext);
                    }
                    pow(a_i, (b_ext.first() * pow(10, i as nat) + Self::digits_to_nat(b_ext.drop_first())) as nat) % m_i; {
                        broadcast use lemma_pow_adds;
                    }
                    pow(a_i, (b_ext.first() * pow(10, i as nat)) as nat) * pow(a_i, Self::digits_to_nat(b_ext.drop_first())) % m_i; {
                        broadcast use lemma_mul_mod_noop;
                    }
                    (pow(a_i, (b_ext.first() * pow(10, i as nat)) as nat) % m_i) * (pow(a_i, Self::digits_to_nat(b_ext.drop_first())) % m_i) % m_i; {
                        lemma_mul_is_commutative(b_ext.first() as int, pow(10, i as nat));
                        lemma_pow_multiplies(a_i, pow(10, i as nat) as nat, b_ext.first() as nat);
                    }
                    (pow(pow(a_i, pow(10, i as nat) as nat), b_ext.first() as nat) % m_i) * (pow(a_i, Self::digits_to_nat(b_ext.drop_first())) % m_i) % m_i; {
                        lemma_mod_pow_base(pow(a_i, pow(10, i as nat) as nat), b_ext.first() as nat, m_i);
                    }
                    (pow(pow(a_i, pow(10, i as nat) as nat) % m_i, b_ext.first() as nat) % m_i) * (pow(a_i, Self::digits_to_nat(b_ext.drop_first())) % m_i) % m_i; {
                        assert(b_ext.drop_first() == b@.skip(b.len()-i));
                    }
                    mp * result % m_i;
                }
                

            }
            result = result * mp % Self::M;
            base_pow = Self::mod_pow(base_pow, 10, Self::M);
            i += 1;
        }
        proof {
            lemma_seq_skip_nothing(b@, b.len() - i);
        }
        result as i32
    }
}

} 
