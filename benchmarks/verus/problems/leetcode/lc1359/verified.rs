use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_mul_mod_noop, lemma_mul_mod_noop_right};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_count(n: int) -> int
        decreases n,
    {
        if n <= 1 {
            1
        } else {
            Self::valid_count(n - 1) * n * (2 * n - 1)
        }
    }

    proof fn lemma_valid_count_positive(n: int)
        requires
            n >= 1,
        ensures
            Self::valid_count(n) >= 1,
        decreases n,
    {
        if n > 1 {
            Self::lemma_valid_count_positive(n - 1);
            let prev = Self::valid_count(n - 1);
            assert(prev * n * (2 * n - 1) >= 1) by(nonlinear_arith)
                requires prev >= 1, n >= 2;
        }
    }

    pub fn count_orders(n: i32) -> (result: i32)
        requires
            1 <= n <= 500,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Self::valid_count(n as int) % 1_000_000_007,
    {
        let m: i64 = 1_000_000_007;
        let mut count: i64 = 1;
        let mut i: i64 = 2;

        while i <= n as i64
            invariant
                2 <= i <= n as i64 + 1,
                0 <= count < 1_000_000_007,
                m == 1_000_000_007i64,
                1 <= n <= 500,
                count as int == Self::valid_count((i - 1) as int) % 1_000_000_007,
            decreases n as i64 + 1 - i,
        {
            proof {
                assert(i as int <= n as int <= 500);
                assert((2 * i as int - 1) * (i as int) >= 0) by(nonlinear_arith)
                    requires i as int >= 2;
                assert((2 * i as int - 1) * (i as int) <= 499_500) by(nonlinear_arith)
                    requires 2 <= i as int <= 500;
            }

            let factor: i64 = (2 * i - 1) * i;

            proof {
                let vc = Self::valid_count((i - 1) as int);
                let b = i as int * (2 * i as int - 1);
                let m_int: int = 1_000_000_007;

                Self::lemma_valid_count_positive((i - 1) as int);

                assert(Self::valid_count(i as int) == vc * i as int * (2 * i as int - 1));
                assert(vc * i as int * (2 * i as int - 1) == vc * b) by(nonlinear_arith)
                    requires b == i as int * (2 * i as int - 1);

                lemma_mul_mod_noop(vc, b, m_int);
                lemma_mul_mod_noop_right(vc % m_int, b, m_int);

                assert(((vc % m_int) * b) % m_int == (vc * b) % m_int);
                assert(factor as int == b) by(nonlinear_arith)
                    requires factor as int == (2 * i as int - 1) * (i as int),
                        b == i as int * (2 * i as int - 1);
                assert((count as int * factor as int) % m_int == Self::valid_count(i as int) % m_int);

                let cv = count as int;
                let fv = factor as int;
                assert(cv * fv < 500_000_000_000_000int) by(nonlinear_arith)
                    requires 0 <= cv < 1_000_000_007, 0 <= fv <= 499_500;
            }

            count = (count * factor) % m;
            i += 1;
        }

        count as i32
    }
}

}
