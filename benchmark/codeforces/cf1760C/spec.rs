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
    }
}

}
