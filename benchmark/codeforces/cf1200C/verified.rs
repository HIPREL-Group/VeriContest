use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

fn main() {}

verus! {

proof fn lemma_spec_gcd_u64_min(a: u64, b: u64)
    requires
        a >= 1,
        b >= 1,
    ensures
        Solution::spec_gcd_u64(a, b) >= 1,
    decreases b,
{
    reveal_with_fuel(Solution::spec_gcd_u64, 2);
    assert(Solution::spec_gcd_u64(a, b) == Solution::spec_gcd_u64(b, a % b));
    let r = a % b;
    if r == 0 {
        assert(Solution::spec_gcd_u64(a, b) == Solution::spec_gcd_u64(b, 0));
        reveal_with_fuel(Solution::spec_gcd_u64, 1);
        assert(Solution::spec_gcd_u64(b, 0) == b);
        assert(b >= 1);
    } else {
        lemma_spec_gcd_u64_min(b, r);
    }
}

proof fn lemma_spec_gcd_u64_le_min(a: u64, b: u64)
    requires
        a >= 1,
        b >= 1,
    ensures
        Solution::spec_gcd_u64(a, b) <= a,
        Solution::spec_gcd_u64(a, b) <= b,
    decreases b,
{
    reveal_with_fuel(Solution::spec_gcd_u64, 2);
    let r = a % b;
    assert(Solution::spec_gcd_u64(a, b) == Solution::spec_gcd_u64(b, r));
    if r == 0 {
        reveal_with_fuel(Solution::spec_gcd_u64, 1);
        assert(Solution::spec_gcd_u64(a, b) == b);
        assert(a % b == 0);
        if b > a {
            let ai = a as int;
            let bi = b as int;
            assert(0 <= ai && ai < bi);
            lemma_basic_div(ai, bi);
            lemma_fundamental_div_mod(ai, bi);
            assert(ai % bi == ai);
            assert(a % b == a);
            assert(a % b == 0);
            assert(a == 0);
            assert(false);
        }
        assert(b <= a);
        assert(Solution::spec_gcd_u64(a, b) <= a);
        assert(Solution::spec_gcd_u64(a, b) <= b);
    } else {
        lemma_spec_gcd_u64_le_min(b, r);
        assert(Solution::spec_gcd_u64(a, b) == Solution::spec_gcd_u64(b, r));
        assert(Solution::spec_gcd_u64(b, r) <= b);
        assert(Solution::spec_gcd_u64(b, r) <= r);
        assert(r < b);
        if a < b {
            let ai = a as int;
            let bi = b as int;
            assert(0 <= ai && ai < bi);
            lemma_basic_div(ai, bi);
            lemma_fundamental_div_mod(ai, bi);
            assert(ai % bi == ai);
            assert(r == a);
            assert(r <= a);
        } else {
            assert(b <= a);
            assert(r < b);
            assert(r <= a);
        }
        assert(Solution::spec_gcd_u64(a, b) <= a);
        assert(Solution::spec_gcd_u64(a, b) <= b);
    }
}

proof fn lemma_u64_quot_ge_one(nu: u64, g: u64)
    requires
        nu >= g,
        g >= 1,
    ensures
        nu / g >= 1,
{
    let ni = nu as int;
    let gi = g as int;
    assert(gi <= ni);
    assert(0 < gi);
    lemma_div_is_ordered(gi, ni, gi);
    assert(gi / gi <= ni / gi);
    assert(gi / gi == 1);
    assert(nu / g >= 1);
}

pub struct Solution;

impl Solution {
    pub open spec fn spec_gcd_u64(a: u64, b: u64) -> u64
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::spec_gcd_u64(b, a % b)
        }
    }

    pub open spec fn spec_component_id_u64(n: u64, m: u64, t: int, y: int) -> int
        recommends
            n > 0,
            m > 0,
            t == 1 || t == 2,
    {
        let g = Self::spec_gcd_u64(n, m);
        let n2 = n / g;
        let m2 = m / g;
        if t == 1 {
            (y - 1) / (n2 as int)
        } else {
            (y - 1) / (m2 as int)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn corridor_same_component(
        n: i64,
        m: i64,
        t1: i32,
        y1: i64,
        t2: i32,
        y2: i64,
    ) -> (result: bool)
        requires
            1 <= n <= 1_000_000_000_000_000_000,
            1 <= m <= 1_000_000_000_000_000_000,
            t1 == 1 || t1 == 2,
            t2 == 1 || t2 == 2,
            t1 == 1 ==> 1 <= y1 <= n,
            t1 == 2 ==> 1 <= y1 <= m,
            t2 == 1 ==> 1 <= y2 <= n,
            t2 == 2 ==> 1 <= y2 <= m,
        ensures
            result == (Self::spec_component_id_u64(n as u64, m as u64, t1 as int, y1 as int)
                == Self::spec_component_id_u64(n as u64, m as u64, t2 as int, y2 as int)),
    {
        let nu = n as u64;
        let mu = m as u64;
        proof {
            assert(nu >= 1);
            assert(mu >= 1);
        }
        let mut a: u64 = nu;
        let mut b: u64 = mu;
        while b != 0
            invariant
                nu > 0,
                mu > 0,
                Self::spec_gcd_u64(a, b) == Self::spec_gcd_u64(nu, mu),
            decreases b,
        {
            let rem: u64 = a % b;
            proof {
                assert(Self::spec_gcd_u64(a, b) == Self::spec_gcd_u64(b, a % b));
                assert(a % b == rem);
            }
            a = b;
            b = rem;
        }
        let g = a;
        proof {
            lemma_spec_gcd_u64_min(nu, mu);
            assert(Self::spec_gcd_u64(a, b) == Self::spec_gcd_u64(nu, mu));
            assert(b == 0);
            assert(Self::spec_gcd_u64(a, 0) == a);
            assert(a == Self::spec_gcd_u64(nu, mu));
            assert(a >= 1);
            assert(g >= 1);
            lemma_spec_gcd_u64_le_min(nu, mu);
            assert(g <= nu);
            assert(g <= mu);
            lemma_u64_quot_ge_one(nu, g);
            lemma_u64_quot_ge_one(mu, g);
        }
        let n2 = nu / g;
        let m2 = mu / g;
        proof {
            assert(n2 >= 1);
            assert(m2 >= 1);
        }
        let c1 = if t1 == 1 {
            (y1 - 1) / (n2 as i64)
        } else {
            (y1 - 1) / (m2 as i64)
        };
        let c2 = if t2 == 1 {
            (y2 - 1) / (n2 as i64)
        } else {
            (y2 - 1) / (m2 as i64)
        };
        proof {
            assert(c1 as int == Self::spec_component_id_u64(nu, mu, t1 as int, y1 as int));
            assert(c2 as int == Self::spec_component_id_u64(nu, mu, t2 as int, y2 as int));
        }
        c1 == c2
    }
}

}
