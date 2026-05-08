use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn removable_pairs_prefix(s: Seq<i64>, n: int, pairs: int) -> bool
        recommends
            0 <= pairs <= n,
            n == s.len(),
    {
        forall|k: int| 0 <= k < pairs ==> #[trigger] s[k] + s[n - 1 - k] == 1
    }

    pub open spec fn feasible_original_len(s: Seq<i64>, original_len: int) -> bool
        recommends
            s.len() >= 1,
    {
        let n = s.len() as int;
        &&& 0 <= original_len <= n
        &&& (n - original_len) % 2 == 0
        &&& Self::removable_pairs_prefix(s, n, (n - original_len) / 2)
    }

    pub fn shortest_original(n: usize, s: Vec<i64>) -> (result: usize)
        requires
            n >= 1,
            s.len() == n,
            forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
        ensures
            Self::feasible_original_len(s@, result as int),
            forall|r2: int| 0 <= r2 < result as int ==> !Self::feasible_original_len(s@, r2),
    {
    }
}

}
