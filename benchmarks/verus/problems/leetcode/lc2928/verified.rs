use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_b(n: nat, limit: nat, a: nat, b: nat) -> bool {
        a <= limit && b <= limit && a + b <= n && n - a - b <= limit
    }

    pub open spec fn count_b_prefix(n: nat, limit: nat, a: nat, kb: nat) -> nat
        decreases kb,
    {
        if kb == 0 {
            0
        } else {
            Self::count_b_prefix(n, limit, a, (kb - 1) as nat)
                + if Self::valid_b(n, limit, a, (kb - 1) as nat) { 1nat } else { 0nat }
        }
    }

    pub open spec fn count_a_prefix(n: nat, limit: nat, ka: nat) -> nat
        decreases ka,
    {
        if ka == 0 {
            0
        } else {
            Self::count_a_prefix(n, limit, (ka - 1) as nat)
                + Self::count_b_prefix(n, limit, (ka - 1) as nat, (limit + 1) as nat)
        }
    }

    pub open spec fn total_ways(n: nat, limit: nat) -> nat {
        Self::count_a_prefix(n, limit, (limit + 1) as nat)
    }

    pub fn distribute_candies(n: i32, limit: i32) -> (result: i32)
        requires
            1 <= n <= 50,
            1 <= limit <= 50,
        ensures
            result as nat == Self::total_ways(n as nat, limit as nat),
            0 <= result <= 2601,
    {
        let mut a: i32 = 0;
        let mut total: i32 = 0;
        while a <= limit
            invariant
                0 <= a <= limit + 1,
                0 <= total <= 2601,
                total <= a * (limit + 1),
                total as nat == Self::count_a_prefix(n as nat, limit as nat, a as nat),
                1 <= n <= 50,
                1 <= limit <= 50,
            decreases limit - a + 1,
        {
            let mut b: i32 = 0;
            while b <= limit
                invariant
                    0 <= b <= limit + 1,
                    0 <= total <= 2601,
                    total <= a * (limit + 1) + b,
                    total as nat
                        == Self::count_a_prefix(n as nat, limit as nat, a as nat)
                            + Self::count_b_prefix(n as nat, limit as nat, a as nat, b as nat),
                    0 <= a <= limit,
                    1 <= n <= 50,
                    1 <= limit <= 50,
                decreases limit - b + 1,
            {
                let c = n - a - b;
                if 0 <= c && c <= limit {
                    assert(a <= limit);
                    assert(b <= limit);
                    proof {
                        assert(a * (limit + 1) + b <= 2600) by (nonlinear_arith)
                            requires
                                0 <= a,
                                a <= limit,
                                0 <= b,
                                b <= limit,
                                1 <= limit,
                                limit <= 50;
                    }
                    assert(total <= a * (limit + 1) + b);
                    assert(total <= 2600);
                    total = total + 1;
                }
                assert(b + 1 <= limit + 1);
                b = b + 1;
                proof {
                    assert(Self::count_b_prefix(n as nat, limit as nat, a as nat, b as nat)
                        == Self::count_b_prefix(n as nat, limit as nat, a as nat, ((b - 1) as nat))
                            + if Self::valid_b(n as nat, limit as nat, a as nat, ((b - 1) as nat)) { 1nat } else { 0nat });
                }
            }

            assert(b == limit + 1);
            assert(total <= a * (limit + 1) + (limit + 1));
            proof {
                assert(total <= (a + 1) * (limit + 1)) by (nonlinear_arith)
                    requires
                        total <= a * (limit + 1) + (limit + 1),
                        0 <= a,
                        1 <= limit;
            }
            a = a + 1;
            proof {
                assert(Self::count_a_prefix(n as nat, limit as nat, a as nat)
                    == Self::count_a_prefix(n as nat, limit as nat, ((a - 1) as nat))
                        + Self::count_b_prefix(n as nat, limit as nat, ((a - 1) as nat), (limit + 1) as nat));
            }
        }

        total
    }
}

}
