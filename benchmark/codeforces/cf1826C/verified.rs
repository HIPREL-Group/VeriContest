use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_first_divisor_from(n: int, d: int) -> int
        recommends
            n >= 1,
            d >= 2,
        decreases if d <= n { n - d + 1 } else { 0 },
    {
        if d > n || d * d > n {
            n
        } else if n % d == 0 {
            d
        } else {
            Self::spec_first_divisor_from(n, d + 1)
        }
    }

    pub open spec fn spec_freedom_possible(n: int, m: int) -> bool {
        if n == 1 {
            true
        } else if m >= n {
            false
        } else {
            Self::spec_first_divisor_from(n, 2) > m
        }
    }

    proof fn lemma_first_divisor_found(n: int, d: int)
        requires
            n >= 1,
            d >= 2,
            d <= n,
            d * d <= n,
            n % d == 0,
        ensures
            Self::spec_first_divisor_from(n, d) == d,
        decreases n - d + 1,
    {
        reveal_with_fuel(Solution::spec_first_divisor_from, 2);
    }

    proof fn lemma_first_divisor_step(n: int, d: int)
        requires
            n >= 1,
            d >= 2,
            d <= n,
            d * d <= n,
            n % d != 0,
        ensures
            Self::spec_first_divisor_from(n, d) == Self::spec_first_divisor_from(n, d + 1),
        decreases n - d + 1,
    {
        reveal_with_fuel(Solution::spec_first_divisor_from, 2);
    }

    proof fn lemma_first_divisor_base(n: int, d: int)
        requires
            n >= 1,
            d >= 2,
            d > n || d * d > n,
        ensures
            Self::spec_first_divisor_from(n, d) == n,
    {
        reveal_with_fuel(Solution::spec_first_divisor_from, 2);
    }

    pub fn freedom_possible(n: i64, m: i64) -> (res: bool)
        requires
            1 <= n as int <= 1_000_000_000,
            1 <= m as int <= 1_000_000_000,
        ensures
            res == Self::spec_freedom_possible(n as int, m as int),
    {
        if n == 1 {
            return true;
        }
        if m >= n {
            return false;
        }
        let mut d: i64 = 2;
        while d * d <= n
            invariant
                1 < n as int <= 1_000_000_000,
                1 <= m as int <= 1_000_000_000,
                (m as int) < (n as int),
                2 <= d as int,
                d as int <= n as int,
                d as int * d as int <= 1_000_000_000_000_000_000,
                Self::spec_first_divisor_from(n as int, d as int)
                    == Self::spec_first_divisor_from(n as int, 2),
            decreases n as int - d as int + 1,
        {
            if n % d == 0 {
                proof {
                    Self::lemma_first_divisor_found(n as int, d as int);
                    assert(Self::spec_first_divisor_from(n as int, 2) == d as int);
                    assert(Self::spec_freedom_possible(n as int, m as int) == (d as int > m as int));
                }
                return d > m;
            }
            proof {
                Self::lemma_first_divisor_step(n as int, d as int);
                assert(d as int + 1 <= n as int) by (nonlinear_arith)
                    requires
                        d as int >= 2,
                        d as int * d as int <= n as int,
                ;
                assert(d as int + 1 <= 1_000_000_000);
                assert((d as int + 1) * (d as int + 1) <= 1_000_000_000_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= d as int + 1,
                        d as int + 1 <= 1_000_000_000,
                        1_000_000_000i64 * 1_000_000_000i64 == 1_000_000_000_000_000_000i64,
                ;
            }
            d = d + 1;
        }
        proof {
            Self::lemma_first_divisor_base(n as int, d as int);
            assert(Self::spec_first_divisor_from(n as int, 2) == n as int);
            assert(n as int > m as int);
        }
        true
    }
}

}