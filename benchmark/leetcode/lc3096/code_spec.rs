use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn level_score(x: i32) -> int {
        if x == 1 { 1 } else { -1 }
    }

    pub open spec fn prefix_score(possible: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= possible.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_score(possible, end - 1) + Self::level_score(possible[end - 1])
        }
    }

    pub open spec fn alice_wins_after_k(possible: Seq<i32>, k: int) -> bool {
        &&& 1 <= k < possible.len()
        &&& 2 * Self::prefix_score(possible, k) > Self::prefix_score(possible, possible.len() as int)
    }

    pub fn minimum_levels(possible: Vec<i32>) -> (result: i32)
        requires
            2 <= possible.len() <= 100000,
            forall |i: int| 0 <= i < possible.len() ==> (#[trigger] possible[i] == 0 || #[trigger] possible[i] == 1),
        ensures
            result == -1 ==> forall |k: int| 1 <= k < possible.len() ==> !Self::alice_wins_after_k(possible@, k),
            result != -1 ==> (
                1 <= result as int && (result as int) < possible.len()
                && Self::alice_wins_after_k(possible@, result as int)
                && forall |k: int| 1 <= k < result as int ==> !Self::alice_wins_after_k(possible@, k)
            ),
    {
        let n = possible.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            let delta: i64 = if possible[i] == 1 { 1 } else { -1 };
            total = total + delta;
            i += 1;
        }

        let mut prefix: i64 = 0;
        i = 0;

        while i < n - 1 {
            let delta: i64 = if possible[i] == 1 { 1 } else { -1 };
            prefix = prefix + delta;
            if 2 * prefix > total {
                return (i + 1) as i32;
            }
            i += 1;
        }

        -1
    }
}

}
