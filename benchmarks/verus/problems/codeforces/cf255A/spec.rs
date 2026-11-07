use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_group(seq: Seq<i64>, end: int, g: int) -> int
        recommends
            0 <= g < 3,
            0 <= end <= seq.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let prev = end - 1;
            Self::sum_group(seq, prev, g) + (if prev % 3 == g { seq[prev] as int } else { 0 })
        }
    }

    pub open spec fn unambiguous_workout(seq: Seq<i64>) -> bool {
        let s0 = Self::sum_group(seq, seq.len() as int, 0);
        let s1 = Self::sum_group(seq, seq.len() as int, 1);
        let s2 = Self::sum_group(seq, seq.len() as int, 2);
        !((s0 >= s1 && s0 >= s2 && (s1 == s0 || s2 == s0))
            || (s1 >= s0 && s1 >= s2 && (s0 == s1 || s2 == s1))
            || (s2 >= s0 && s2 >= s1 && (s0 == s2 || s1 == s2)))
    }

    pub fn workout_sums(a: Vec<i64>) -> (result: (i64, i64, i64))
        requires
            1 <= a.len() <= 20,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 25,
            Self::unambiguous_workout(a@),
        ensures
            result.0 as int == Solution::sum_group(a@, a.len() as int, 0),
            result.1 as int == Solution::sum_group(a@, a.len() as int, 1),
            result.2 as int == Solution::sum_group(a@, a.len() as int, 2),
    {
    }
}

}
