use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_gcd_nat(a: nat, b: nat) -> nat
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::spec_gcd_nat(b, a % b)
        }
    }

    pub open spec fn spec_gcd(a: int, b: int) -> int
        recommends
            0 <= a,
            0 <= b,
    {
        Self::spec_gcd_nat(a as nat, b as nat) as int
    }

    pub open spec fn spec_total_gcd_from(a: Seq<i64>, i: int, cur: int) -> int
        recommends
            0 <= i <= a.len(),
            0 <= cur,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j],
        decreases a.len() - i,
    {
        if i >= a.len() {
            cur
        } else {
            Self::spec_total_gcd_from(a, i + 1, Self::spec_gcd(cur, a[i] as int))
        }
    }

    pub open spec fn spec_total_gcd(a: Seq<i64>) -> int
        recommends
            1 <= a.len(),
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j],
    {
        Self::spec_total_gcd_from(a, 1, a[0] as int)
    }

    pub open spec fn spec_divisor_contrib(g: int, d: int) -> int
        recommends
            1 <= g,
            1 <= d,
            d <= g / d,
    {
        if g % d == 0 {
            if d == g / d {
                1int
            } else {
                2int
            }
        } else {
            0int
        }
    }

    pub open spec fn spec_count_divisors_from(g: int, d: int) -> int
        recommends
            1 <= g,
            1 <= d,
            d <= g + 1,
        decreases g - d + 1,
    {
        if d > g {
            0int
        } else if d > g / d {
            0int
        } else {
            Self::spec_divisor_contrib(g, d) + Self::spec_count_divisors_from(g, d + 1)
        }
    }

    pub open spec fn spec_count_divisors(g: int) -> int {
        if g <= 0 {
            0int
        } else {
            Self::spec_count_divisors_from(g, 1)
        }
    }

    pub fn count_common_divisors(n: usize, a: Vec<i64>) -> (res: i64)
        requires
            1 <= n <= 400000,
            a.len() == n,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= 1000000000000i64,
        ensures
            res as int == Self::spec_count_divisors(Self::spec_total_gcd(a@)),
    {
    }
}

}
