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
        let mut g: i64 = a[0];
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= n <= 400000,
                a.len() == n,
                1 <= i <= n,
                1 <= g <= 1000000000000i64,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] a[j] <= 1000000000000i64,
                Self::spec_total_gcd_from(a@, i as int, g as int) == Self::spec_total_gcd(a@),
            decreases n - i,
        {
            let ghost start_g = g as int;
            let mut x: i64 = g;
            let mut y: i64 = a[i];
            while y != 0
                invariant
                    1 <= n <= 400000,
                    a.len() == n,
                    1 <= i < n,
                1 <= start_g <= 1000000000000,
                    1 <= x <= 1000000000000i64,
                    0 <= y <= 1000000000000i64,
                    forall|j: int| 0 <= j < n ==> 1 <= #[trigger] a[j] <= 1000000000000i64,
                    Self::spec_gcd(x as int, y as int) == Self::spec_gcd(start_g, a@[i as int] as int),
                decreases y,
            {
                let prev_x = x;
                let prev_y = y;
                let t: i64 = y;
                proof {
                    assert(1 <= prev_x as int);
                    assert(1 <= prev_y as int);
                    assert(Self::spec_gcd(prev_x as int, prev_y as int) == Self::spec_gcd(prev_y as int, (prev_x % prev_y) as int));
                }
                y = x % y;
                x = t;
                proof {
                    assert(x == prev_y);
                    assert(y == prev_x % prev_y);
                    assert(Self::spec_gcd(x as int, y as int) == Self::spec_gcd(start_g, a@[i as int] as int));
                }
            }
            proof {
                assert(y == 0);
                assert(Self::spec_gcd(x as int, 0) == x as int);
                assert(x as int == Self::spec_gcd(start_g, a@[i as int] as int));
                assert(Self::spec_total_gcd_from(a@, i as int, start_g) == Self::spec_total_gcd_from(a@, i as int + 1, Self::spec_gcd(start_g, a@[i as int] as int)));
                assert(Self::spec_total_gcd_from(a@, i as int + 1, x as int) == Self::spec_total_gcd(a@));
            }
            g = x;
            i = i + 1;
        }
        let mut count: i64 = 0;
        let mut d: i64 = 1;
        while d <= g / d
            invariant
                1 <= n <= 400000,
                a.len() == n,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] a[j] <= 1000000000000i64,
                1 <= g <= 1000000000000i64,
                g as int == Self::spec_total_gcd(a@),
                1 <= d <= g + 1,
                0 <= count,
                count as int <= 2 * (d as int - 1),
                count as int + Self::spec_count_divisors_from(g as int, d as int) == Self::spec_count_divisors(g as int),
            decreases g + 1 - d,
        {
            if g % d == 0 {
                proof {
                    assert(d <= g / d);
                    assert(d as int * d as int <= g as int) by (nonlinear_arith)
                        requires
                            0 <= d as int,
                            d as int <= g as int / d as int,
                            1 <= g as int,
                    ;
                    assert(d as int * d as int <= 1000000000000) by (nonlinear_arith)
                        requires
                            d as int * d as int <= g as int,
                            g as int <= 1000000000000,
                    ;
                    assert(d as int <= 1000000) by (nonlinear_arith)
                        requires
                            0 <= d as int,
                            d as int * d as int <= 1000000000000,
                    ;
                    assert(count as int <= 2 * (d as int - 1));
                    assert(count as int + 2 <= 2000000) by (nonlinear_arith)
                        requires
                            count as int <= 2 * (d as int - 1),
                            d as int <= 1000000,
                    ;
                }
                count = count + 1;
                if d != g / d {
                    count = count + 1;
                }
            }
            proof {
                assert(d <= g / d);
                assert(Self::spec_count_divisors_from(g as int, d as int) == Self::spec_divisor_contrib(g as int, d as int) + Self::spec_count_divisors_from(g as int, d as int + 1));
                if g % d == 0 {
                    if d == g / d {
                        assert(Self::spec_divisor_contrib(g as int, d as int) == 1);
                    } else {
                        assert(Self::spec_divisor_contrib(g as int, d as int) == 2);
                    }
                } else {
                    assert(Self::spec_divisor_contrib(g as int, d as int) == 0);
                }
                assert(count as int <= 2 * d as int);
                assert(count as int + Self::spec_count_divisors_from(g as int, d as int + 1) == Self::spec_count_divisors(g as int));
            }
            d = d + 1;
        }
        proof {
            assert(d > g / d);
            assert(Self::spec_count_divisors_from(g as int, d as int) == 0);
            assert(count as int == Self::spec_count_divisors(g as int));
            assert(g as int == Self::spec_total_gcd(a@));
        }
        count
    }
}

}
