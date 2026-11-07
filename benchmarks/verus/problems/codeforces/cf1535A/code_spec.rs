use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max2(a: i64, b: i64) -> i64 {
        if a >= b { a } else { b }
    }

    pub open spec fn min2(a: i64, b: i64) -> i64 {
        if a <= b { a } else { b }
    }

    pub open spec fn fair_playoff_spec(s1: i64, s2: i64, s3: i64, s4: i64) -> bool {
        Self::min2(Self::max2(s1, s2), Self::max2(s3, s4)) > Self::max2(Self::min2(s1, s2), Self::min2(s3, s4))
    }

    pub fn fair_playoff(s1: i64, s2: i64, s3: i64, s4: i64) -> (result: bool)
        requires
            1 <= s1 <= 100,
            1 <= s2 <= 100,
            1 <= s3 <= 100,
            1 <= s4 <= 100,
            s1 != s2,
            s1 != s3,
            s1 != s4,
            s2 != s3,
            s2 != s4,
            s3 != s4,
        ensures
            result == Self::fair_playoff_spec(s1, s2, s3, s4),
    {
        let w1 = if s1 >= s2 { s1 } else { s2 };
        let w2 = if s3 >= s4 { s3 } else { s4 };
        let l1 = if s1 <= s2 { s1 } else { s2 };
        let l2 = if s3 <= s4 { s3 } else { s4 };
        let weaker_winner = if w1 <= w2 { w1 } else { w2 };
        let stronger_loser = if l1 >= l2 { l1 } else { l2 };
        weaker_winner > stronger_loser
    }
}

}
