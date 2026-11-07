use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_array(pref: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= pref.len() <= 100_000,
            forall |i: int| 0 <= i < pref.len() ==> 0 <= #[trigger] pref[i] <= 1_000_000,
        ensures
            result.len() == pref.len(),
            result[0] == pref[0],
            forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i],
            forall |i: int| 1 <= i < pref.len() ==>
                pref[i] == (#[trigger] pref[i - 1]) ^ result[i],
    {
    }
}

}
