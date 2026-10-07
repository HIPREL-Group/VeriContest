use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub fn sum_zero(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == n as int,
            Self::seq_sum(result@, result@.len() as int) == 0,
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j],
    {
        let mut ans: Vec<i32> = Vec::new();
        let half = n / 2;
        let mut i: i32 = 1;
        while i <= half {
            let i0 = i;
            ans.push(i0);
            let neg_i0: i32 = -i0;
            ans.push(neg_i0);
            i = i + 1;
        }
        if n % 2 == 1 {
            ans.push(0);
        }
        ans
    }
}

}
