use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn matches_spec(n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else if n % 2 == 0 {
            n / 2 + Self::matches_spec(n / 2)
        } else {
            (n - 1) / 2 + Self::matches_spec((n - 1) / 2 + 1)
        }
    }

    proof fn lemma_matches_formula(n: int)
        requires n >= 1,
        ensures Self::matches_spec(n) == n - 1,
        decreases n,
    {
        if n > 1 {
            if n % 2 == 0 {
                Self::lemma_matches_formula(n / 2);
            } else {
                Self::lemma_matches_formula((n - 1) / 2 + 1);
            }
        }
    }

    pub fn number_of_matches(n: i32) -> (result: i32)
        requires
            1 <= n <= 200,
        ensures
            result == Self::matches_spec(n as int),
    {
        proof {
            Self::lemma_matches_formula(n as int);
        }
        n - 1
    }
}

}
