use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs_i(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

pub open spec fn spec_good_pair_at_k(s: Seq<i64>, i1: int, j1: int, k: int) -> bool {
    let vi = s[i1 - 1] as int;
    let vj = s[j1 - 1] as int;
    let vk = s[k - 1] as int;
    spec_abs_i(vi - vk) + spec_abs_i(vk - vj) == spec_abs_i(vi - vj)
}

impl Solution {
    pub fn good_pair_indices(a: Vec<i64>) -> (res: (i64, i64))
        requires
            1 <= a.len() <= 200_000,
            forall|t: int| 0 <= t < a.len() ==> #[trigger] (a[t] as int) >= 1,
        ensures
            1 <= res.0 as int <= a.len() as int,
            1 <= res.1 as int <= a.len() as int,
            forall|k: int|
                1 <= k <= a.len() ==> #[trigger] spec_good_pair_at_k(a@, res.0 as int, res.1 as int, k),
    {
    }
}

}
