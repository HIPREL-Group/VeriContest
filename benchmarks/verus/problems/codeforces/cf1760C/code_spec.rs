use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn valid_advantage(s: Seq<i64>, i: int, d: int) -> bool {
    exists|j: int| {
        &&& 0 <= j < s.len()
        &&& j != i
        &&& d == s[i] as int - s[j] as int
        &&& forall|k: int| 0 <= k < s.len() && k != i ==> s[k] as int <= #[trigger] s[j] as int
    }
}

pub struct Solution;

impl Solution {
    pub fn advantages(s: Vec<i64>) -> (result: Vec<i64>)
        requires
            2 <= s.len() <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000,
        ensures
            result.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> valid_advantage(s@, i, result[i] as int),
    {
        let n = s.len();
        let mut max1: i64 = s[0];
        let mut idx1: usize = 0;
        let mut max2: i64 = s[1];
        let mut idx2: usize = 1;

        if max2 > max1 {
            let tv = max1;
            let ti = idx1;
            max1 = max2;
            idx1 = idx2;
            max2 = tv;
            idx2 = ti;
        }

        let mut t: usize = 2;
        while t < n {
            if s[t] > max1 {
                max2 = max1;
                idx2 = idx1;
                max1 = s[t];
                idx1 = t;
            } else if s[t] > max2 {
                max2 = s[t];
                idx2 = t;
            }
            t = t + 1;
        }

        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            let best: i64;
            if i == idx1 {
                best = max2;
            } else {
                best = max1;
            }

            result.push(s[i] - best);
            i = i + 1;
        }

        result
    }
}

}
