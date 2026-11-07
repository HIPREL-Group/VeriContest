use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn clumsy_rest(m: int) -> int
        decreases m,
    {
        if m <= 0 { 0 }
        else if m == 1 { 1 }
        else if m == 2 { m * (m - 1) }
        else if m == 3 { m * (m - 1) / (m - 2) }
        else { m * (m - 1) / (m - 2) - (m - 3) + Solution::clumsy_rest(m - 4) }
    }

    pub open spec fn clumsy_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else if n == 1 { 1 }
        else if n == 2 { n * (n - 1) }
        else if n == 3 { n * (n - 1) / (n - 2) }
        else { n * (n - 1) / (n - 2) + (n - 3) - Solution::clumsy_rest(n - 4) }
    }

    proof fn div_unique(a: int, b: int, q: int, r: int)
        requires
            b > 0,
            a == q * b + r,
            0 <= r,
            r < b,
        ensures
            a / b == q,
    {
        lemma_fundamental_div_mod(a, b);
        let qv = a / b;
        let rv = a % b;
        if qv > q {
            assert(qv >= q + 1);
            assert(b * qv >= b * (q + 1)) by(nonlinear_arith)
                requires qv >= q + 1, b > 0;
            assert(b * (q + 1) == q * b + b) by(nonlinear_arith);
            assert(b * qv >= q * b + b);
            assert(a == b * qv + rv);
            assert(a >= q * b + b);
            assert(a == q * b + r);
            assert(a < q * b + b);
            assert(false);
        }
        if qv < q {
            assert(qv <= q - 1);
            assert(b * qv <= b * (q - 1)) by(nonlinear_arith)
                requires qv <= q - 1, b > 0;
            assert(b * (q - 1) == q * b - b) by(nonlinear_arith);
            assert(b * qv <= q * b - b);
            assert(a == b * qv + rv);
            assert(rv < b);
            assert(a <= q * b - b + b - 1);
            assert(a <= q * b - 1);
            assert(a == q * b + r);
            assert(r >= 0);
            assert(a >= q * b);
            assert(false);
        }
    }

    proof fn div_m_identity(m: int)
        requires
            m >= 5,
        ensures
            m * (m - 1) / (m - 2) == m + 1,
    {
        assert(m * (m - 1) == (m + 1) * (m - 2) + 2) by(nonlinear_arith)
            requires m >= 5;
        Solution::div_unique(m * (m - 1), m - 2, m + 1, 2);
    }

    proof fn div_m_bound(m: int)
        requires
            m >= 4,
        ensures
            m + 1 <= m * (m - 1) / (m - 2) <= m + 2,
    {
        if m == 4 {
        } else {
            Solution::div_m_identity(m);
        }
    }

    proof fn clumsy_rest_lower_bound(m: int)
        requires
            0 <= m <= 10000,
        ensures
            Solution::clumsy_rest(m) >= 0,
        decreases m,
    {
        if m <= 3 {
        } else {
            Solution::clumsy_rest_lower_bound(m - 4);
            Solution::div_m_bound(m);
        }
    }

    #[verifier::spinoff_prover]
    proof fn clumsy_rest_upper_bound(m: int)
        requires
            0 <= m <= 10000,
        ensures
            Solution::clumsy_rest(m) <= m + 6,
        decreases m,
    {
        if m == 0 {
        } else if m == 1 {
        } else if m == 2 {
        } else if m == 3 {
        } else if m == 4 {
            assert(Solution::clumsy_rest(0) == 0);
        } else {
            Solution::clumsy_rest_upper_bound(m - 4);
            Solution::div_m_identity(m);
        }
    }

    proof fn clumsy_spec_lower_bound(n: int)
        requires
            1 <= n <= 10000,
        ensures
            Solution::clumsy_spec(n) >= 1,
    {
        if n <= 4 {
        } else {
            Solution::clumsy_rest_upper_bound(n - 4);
            Solution::div_m_identity(n);
        }
    }

    proof fn clumsy_spec_upper_bound(n: int)
        requires
            1 <= n <= 10000,
        ensures
            Solution::clumsy_spec(n) <= 2 * n,
    {
        if n <= 3 {
        } else {
            Solution::clumsy_rest_lower_bound(n - 4);
            Solution::div_m_bound(n);
        }
    }

    pub fn clumsy(n: i32) -> (result: i32)
        requires
            1 <= n <= 10000,
        ensures
            result as int == Solution::clumsy_spec(n as int),
    {
        if n == 1 { return 1; }
        if n == 2 { return 2; }
        if n == 3 { return 6; }

        proof {
            assert(n as int * (n as int - 1) <= 99990000) by(nonlinear_arith)
                requires 4 <= n as int <= 10000;
            Solution::div_m_bound(n as int);
            Solution::clumsy_spec_lower_bound(n as int);
            Solution::clumsy_spec_upper_bound(n as int);
            Solution::clumsy_rest_lower_bound((n - 4) as int);
            Solution::clumsy_rest_upper_bound((n - 4) as int);
        }

        let mut result = n * (n - 1) / (n - 2) + (n - 3);
        let mut k = n - 4;

        while k >= 4
            invariant
                0 <= k <= n - 4,
                1 <= n <= 10000,
                result as int == Solution::clumsy_spec(n as int) + Solution::clumsy_rest(k as int),
                1 <= result <= 3 * n,
            decreases k,
        {
            proof {
                Solution::div_m_bound(k as int);
                Solution::clumsy_rest_lower_bound(k as int);
                Solution::clumsy_rest_upper_bound(k as int);
                Solution::clumsy_rest_lower_bound((k - 4) as int);
                Solution::clumsy_rest_upper_bound((k - 4) as int);
                Solution::clumsy_spec_lower_bound(n as int);
                Solution::clumsy_spec_upper_bound(n as int);
                assert(k as int * (k as int - 1) <= 99920020) by(nonlinear_arith)
                    requires 4 <= k as int <= 9996;
            }

            result = result - k * (k - 1) / (k - 2) + (k - 3);
            k = k - 4;
        }

        proof {
            Solution::clumsy_rest_lower_bound(k as int);
            Solution::clumsy_rest_upper_bound(k as int);
        }

        if k == 3 {
            result = result - k * (k - 1) / (k - 2);
        } else if k == 2 {
            result = result - k * (k - 1);
        } else if k == 1 {
            result = result - k;
        }

        result
    }
}

} 
