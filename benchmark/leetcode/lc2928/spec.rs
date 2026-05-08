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
    }
}

}
