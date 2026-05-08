use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_neg_inf() -> int {
    -1_000_000_000_000_000
}

pub open spec fn spec_max2(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_dp_state(b: Seq<i32>, k: nat) -> (int, int, int)
    recommends
        k <= b.len(),
    decreases k,
{
    if k == 0 {
        (spec_neg_inf(), spec_neg_inf(), spec_neg_inf())
    } else {
        let (res0, dp10, dp20) = spec_dp_state(b, (k - 1) as nat);
        let bi = b[(k - 1) as int] as int;
        let ii = (k - 1) as int;
        let cand = dp20 + bi - ii;
        let new_res = spec_max2(res0, cand);
        let new_dp2 = spec_max2(dp20, dp10 + bi);
        let new_dp1 = spec_max2(dp10, bi + ii);
        (new_res, new_dp1, new_dp2)
    }
}

pub open spec fn spec_best_score(b: Seq<i32>) -> int {
    spec_dp_state(b, b.len() as nat).0
}

impl Solution {
    pub fn best_running_miles(b: &Vec<i32>) -> (result: i64)
        requires
            3 <= b.len() <= 100_000,
            forall|j: int|
                #![trigger b[j]]
                0 <= j && j < b.len() ==> 1 <= b[j] as int && b[j] as int <= 100_000_000,
        ensures
            result == spec_best_score(b@),
    {
    }
}

}
