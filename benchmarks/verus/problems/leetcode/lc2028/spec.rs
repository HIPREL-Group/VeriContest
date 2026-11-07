use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
        }
    }

    pub fn missing_rolls(rolls: Vec<i32>, mean: i32, n: i32) -> (res: Vec<i32>)
        requires
            1 <= rolls.len() <= 100_000,
            1 <= n <= 100_000,
            1 <= mean <= 6,
            forall |i: int| 0 <= i < rolls.len() ==> 1 <= #[trigger] rolls[i] <= 6,
        ensures
            (res@ =~= Seq::<i32>::empty()) == (
                mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@) < n as int
                || mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@) > 6 * n as int
            ),
            res@ != Seq::<i32>::empty() ==> (
                res.len() == n as int
                && (forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= 6)
                && Self::seq_sum(res@)
                    == mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@)
            ),
    {
        
    }
}

}
