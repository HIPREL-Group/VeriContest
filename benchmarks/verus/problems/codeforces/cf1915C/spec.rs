use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn total_sum(a: Seq<i64>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::total_sum(a, end - 1) + a[end - 1] as int
        }
    }

    pub open spec fn square_of(s: int) -> int {
        s * s
    }

    pub open spec fn is_perfect_square(val: int) -> bool {
        exists |s: int| 0 <= s && #[trigger] Self::square_of(s) == val
    }

    pub fn can_square(a: Vec<i64>) -> (result: bool)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
        ensures
            result == Self::is_perfect_square(Self::total_sum(a@, a@.len() as int)),
    {
    }
}

}
