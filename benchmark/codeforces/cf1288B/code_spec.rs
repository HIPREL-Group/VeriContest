use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_pow10(k: int) -> int
    recommends
        0 <= k && k <= 12,
{
    if k == 0 {
        1
    } else if k == 1 {
        10
    } else if k == 2 {
        100
    } else if k == 3 {
        1_000
    } else if k == 4 {
        10_000
    } else if k == 5 {
        100_000
    } else if k == 6 {
        1_000_000
    } else if k == 7 {
        10_000_000
    } else if k == 8 {
        100_000_000
    } else if k == 9 {
        1_000_000_000
    } else if k == 10 {
        10_000_000_000
    } else if k == 11 {
        100_000_000_000
    } else {
        1_000_000_000_000
    }
}

pub open spec fn spec_meme_answer(A: int, B: int) -> int {
    (if spec_pow10(1) - 1 <= B { A } else { 0 }) + (if spec_pow10(2) - 1 <= B { A } else { 0 })
        + (if spec_pow10(3) - 1 <= B { A } else { 0 }) + (if spec_pow10(4) - 1 <= B { A } else { 0 })
        + (if spec_pow10(5) - 1 <= B { A } else { 0 }) + (if spec_pow10(6) - 1 <= B { A } else { 0 })
        + (if spec_pow10(7) - 1 <= B { A } else { 0 }) + (if spec_pow10(8) - 1 <= B { A } else { 0 })
        + (if spec_pow10(9) - 1 <= B { A } else { 0 })
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn meme_pair_count(a_max: i64, b_max: i64) -> (res: i64)
        requires
            1 <= a_max <= 1_000_000_000,
            1 <= b_max <= 1_000_000_000,
        ensures
            (res as int) == spec_meme_answer(a_max as int, b_max as int),
    {
        let mut ans: i64 = 0;
        if 9 <= b_max {
            ans = ans + a_max;
        }
        if 99 <= b_max {
            ans = ans + a_max;
        }
        if 999 <= b_max {
            ans = ans + a_max;
        }
        if 9_999 <= b_max {
            ans = ans + a_max;
        }
        if 99_999 <= b_max {
            ans = ans + a_max;
        }
        if 999_999 <= b_max {
            ans = ans + a_max;
        }
        if 9_999_999 <= b_max {
            ans = ans + a_max;
        }
        if 99_999_999 <= b_max {
            ans = ans + a_max;
        }
        if 999_999_999 <= b_max {
            ans = ans + a_max;
        }
        ans
    }
}

}
