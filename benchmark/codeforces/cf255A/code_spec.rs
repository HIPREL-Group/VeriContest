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

    pub fn workout_sums(a: Vec<i64>) -> (result: (i64, i64, i64))
        requires
            1 <= a.len() <= 20,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 25,
        ensures
            result.0 as int == Solution::sum_group(a@, a.len() as int, 0),
            result.1 as int == Solution::sum_group(a@, a.len() as int, 1),
            result.2 as int == Solution::sum_group(a@, a.len() as int, 2),
    {
        let n = a.len();
        let mut chest: i64 = 0;
        let mut biceps: i64 = 0;
        let mut back: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let idx = i;
            if idx % 3 == 0 {
                chest = chest + a[idx];
            } else if idx % 3 == 1 {
                biceps = biceps + a[idx];
            } else {
                back = back + a[idx];
            }
            i = idx + 1;
        }
        (chest, biceps, back)
    }
}

}
