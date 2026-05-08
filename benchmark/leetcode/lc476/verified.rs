use vstd::arithmetic::power2::{
    lemma2_to64, lemma_pow2, lemma_pow2_strictly_increases, lemma_pow2_unfold, pow2,
};
use vstd::arithmetic::div_mod::lemma_div_non_zero;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_length_spec(n: nat) -> nat
        decreases n,
    {
        if n <= 1 { 1 } else { 1 + Solution::bit_length_spec(n / 2) }
    }

    pub open spec fn find_complement_spec(num: nat) -> nat {
        (pow2(Solution::bit_length_spec(num)) - 1 - num) as nat
    }

    pub proof fn lemma_pow2_mono(i: nat, j: nat)
        requires
            i <= j,
        ensures
            pow2(i) <= pow2(j),
    {
        if i < j {
            lemma_pow2_strictly_increases(i, j);
        }
    }

    pub proof fn lemma_pow2_gt(n: nat)
        requires
            n >= 1,
        ensures
            pow2(Self::bit_length_spec(n)) > n,
        decreases n,
    {
        if n <= 1 {
            assert(n == 1);
            assert(Self::bit_length_spec(n) == 1);
            lemma2_to64();
            assert(pow2(Self::bit_length_spec(n)) == 2);
        } else {
            let m = n / 2;
            lemma_div_non_zero(n as int, 2);
            assert(m >= 1) by (nonlinear_arith)
                requires
                    m == n / 2,
                    n / 2 > 0,
                    n > 1,
            {
            }
            Self::lemma_pow2_gt(m);

            assert(Self::bit_length_spec(n) == 1 + Self::bit_length_spec(m));
            lemma_pow2_unfold(1 + Self::bit_length_spec(m));

            assert(pow2(Self::bit_length_spec(m)) >= m + 1);
            assert(pow2(Self::bit_length_spec(n)) == 2 * pow2(Self::bit_length_spec(m)));
            assert(pow2(Self::bit_length_spec(n)) >= 2 * (m + 1));
            assert(2 * (m + 1) > n) by (nonlinear_arith)
                requires
                    m == n / 2,
                    n > 1,
            {
            }
        }
    }

    pub proof fn lemma_bit_length_ge1(n: nat)
        requires
            n >= 1,
        ensures
            Self::bit_length_spec(n) >= 1,
        decreases n,
    {
        if n > 1 {
            Self::lemma_bit_length_ge1(n / 2);
        }
    }

    pub proof fn lemma_pow2_prev_le(n: nat)
        requires
            n >= 1,
        ensures
            pow2((Self::bit_length_spec(n) - 1) as nat) <= n,
        decreases n,
    {
        if n <= 1 {
            assert(n == 1);
            assert(Self::bit_length_spec(n) == 1);
            lemma2_to64();
            assert(pow2((Self::bit_length_spec(n) - 1) as nat) == 1);
        } else {
            let m = n / 2;
            lemma_div_non_zero(n as int, 2);
            assert(m >= 1) by (nonlinear_arith)
                requires
                    m == n / 2,
                    n / 2 > 0,
                    n > 1,
            {
            }

            Self::lemma_pow2_prev_le(m);
            Self::lemma_bit_length_ge1(m);

            assert(Self::bit_length_spec(n) - 1 == Self::bit_length_spec(m));
            lemma_pow2_unfold(Self::bit_length_spec(m));

            assert(pow2(Self::bit_length_spec(m)) == 2 * pow2((Self::bit_length_spec(m) - 1) as nat));
            assert(pow2((Self::bit_length_spec(m) - 1) as nat) <= m);
            assert(pow2(Self::bit_length_spec(m)) <= 2 * m);
            assert(2 * m <= n) by (nonlinear_arith)
                requires
                    m == n / 2,
            {
            }
            assert(pow2((Self::bit_length_spec(n) - 1) as nat) <= n);
        }
    }

    pub proof fn lemma_bit_length_upper(n: nat)
        requires
            1 <= n <= pow2(31) - 1,
        ensures
            Self::bit_length_spec(n) <= 31,
    {
        Self::lemma_pow2_prev_le(n);

        if Self::bit_length_spec(n) > 31 {
            let b = Self::bit_length_spec(n);
            assert(31 <= (b - 1) as nat) by (nonlinear_arith)
                requires
                    b > 31,
            {
            }
            Self::lemma_pow2_mono(31, (b - 1) as nat);
            assert(pow2(31) <= pow2((b - 1) as nat));
            assert(pow2((b - 1) as nat) <= n);
            assert(false) by (nonlinear_arith)
                requires
                    n <= pow2(31) - 1,
                    pow2(31) <= n,
            {
            }
        }
    }

    pub proof fn lemma_loop_condition(n: nat, k: nat)
        requires
            n >= 1,
            k <= Self::bit_length_spec(n),
        ensures
            (pow2(k) <= n) <==> (k < Self::bit_length_spec(n)),
    {
        let b = Self::bit_length_spec(n);

        if k < b {
            Self::lemma_pow2_prev_le(n);
            assert(k <= (b - 1) as nat) by (nonlinear_arith)
                requires
                    k < b,
            {
            }
            Self::lemma_pow2_mono(k, (b - 1) as nat);
            assert(pow2(k) <= pow2((b - 1) as nat));
            assert(pow2((b - 1) as nat) <= n);
            assert(pow2(k) <= n);
        }

        if pow2(k) <= n {
            if !(k < b) {
                assert(k == b);
                Self::lemma_pow2_gt(n);
                assert(pow2(k) > n);
                assert(false);
            }
        }

        if !(k < b) {
            assert(k == b);
            Self::lemma_pow2_gt(n);
            assert(pow2(k) > n);
        }
    }

    pub fn find_complement(num: i32) -> (res: i32)
        requires
            1 <= num <= i32::MAX,
        ensures
            res == Solution::find_complement_spec(num as nat),
    {
        let n = num as u32;
        let mut mask: u32 = 1;
        let ghost target: nat = n as nat;
        let ghost mut k: nat = 0;

        proof {
            lemma2_to64();
            lemma_pow2(31);
            Self::lemma_bit_length_upper(target);
        }

        while mask <= n
            invariant
                1 <= num <= i32::MAX,
                target == n as nat,
                1 <= target <= pow2(31) - 1,
                mask as nat == pow2(k),
                k <= Self::bit_length_spec(target),
            decreases Self::bit_length_spec(target) - k,
        {
            proof {
                Self::lemma_loop_condition(target, k);
                assert(pow2(k) <= target);
                assert(k < Self::bit_length_spec(target));

                Self::lemma_bit_length_upper(target);
                assert(Self::bit_length_spec(target) <= 31);
                assert(k + 1 <= 31) by (nonlinear_arith)
                    requires
                        k < Self::bit_length_spec(target),
                        Self::bit_length_spec(target) <= 31,
                {
                }

                Self::lemma_pow2_mono(k + 1, 31);
                assert(pow2(k + 1) <= pow2(31));
                lemma2_to64();
                assert(pow2(31) <= u32::MAX);
            }

            let old_mask = mask;
            mask = mask * 2;

            proof {
                lemma_pow2_unfold(k + 1);
                k = k + 1;
            }
        }

        proof {
            assert(!(mask <= n));
            assert(mask > n);
            assert(mask as nat > target);

            Self::lemma_loop_condition(target, k);
            assert(!(pow2(k) <= target));

            assert(k == Self::bit_length_spec(target)) by {
                if k < Self::bit_length_spec(target) {
                    Self::lemma_loop_condition(target, k);
                    assert(pow2(k) <= target);
                    assert(false);
                }
            }

            assert(mask as nat == pow2(Self::bit_length_spec(target)));

            assert(mask >= 1);
            assert(mask >= n + 1);
            assert(mask - 1 >= n);

            Self::lemma_bit_length_upper(target);
            Self::lemma_pow2_mono(Self::bit_length_spec(target), 31);
            assert(pow2(Self::bit_length_spec(target)) <= pow2(31));
            assert(mask as nat <= pow2(31));
            assert(mask - 1 - n <= i32::MAX as u32);

            assert((mask - 1 - n) as nat == pow2(Self::bit_length_spec(target)) - 1 - target);
            assert((mask - 1 - n) as i32 == Self::find_complement_spec(target));
        }

        (mask - 1 - n) as i32
    }
}

} 