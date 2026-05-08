use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tri(k: int) -> int
        decreases k,
    {
        if k <= 0 { 0 } else { Self::tri(k - 1) + k }
    }

    pub fn maximum_groups(grades: Vec<i32>) -> (ans: i32)
        requires
            1 <= grades.len() <= 100000,
            forall |i: int| 0 <= i < grades.len() ==> 1 <= #[trigger] grades[i] <= 100000,
        ensures
            0 <= ans,
            Self::tri(ans as int) <= grades.len() as int,
            Self::tri(ans as int + 1) > grades.len() as int,
    {
        let n = grades.len() as i32;
        let mut k: i32 = 0;
        let mut used: i32 = 0;

        while used + (k + 1) <= n {
            k = k + 1;
            used = used + k;
        }

        k
    }
}

}
