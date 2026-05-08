use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_to(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { Self::sum_to(s, n - 1) + s[n - 1] as int }
    }

    pub open spec fn max_to(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else {
            let prev = Self::max_to(s, n - 1);
            let cur = s[n - 1] as int;
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn spec_number_of_weeks(s: Seq<i32>) -> int {
        let total = Self::sum_to(s, s.len() as int);
        let mx = Self::max_to(s, s.len() as int);
        let rest = total - mx;
        if rest >= mx { total } else { 2 * rest + 1 }
    }

    pub fn number_of_weeks(milestones: Vec<i32>) -> (res: i64)
        requires
            1 <= milestones.len() <= 100_000,
            forall |i: int| 0 <= i < milestones.len() ==> 1 <= #[trigger] milestones[i] <= 1_000_000_000,
        ensures
            res == Self::spec_number_of_weeks(milestones@),
    {
    }
}

}
