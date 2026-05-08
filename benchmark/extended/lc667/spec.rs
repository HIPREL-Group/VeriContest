use vstd::prelude::*;
use vstd::seq::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adj_diff(s: Seq<i32>, i: int) -> int {
        if s[i] as int >= s[i + 1] as int {
            s[i] as int - s[i + 1] as int
        } else {
            s[i + 1] as int - s[i] as int
        }
    }

    pub fn construct_array(n: i32, k: i32) -> (result: Vec<i32>)
        requires
            1 <= k < n <= 10_000,
        ensures
            result@.len() == n as int,
            forall |i: int| 0 <= i < result@.len() ==>
                1 <= #[trigger] result@[i] <= n,
            forall |i: int, j: int|
                0 <= i < j < result@.len() ==> result@[i] != result@[j],
            exists |indices: Seq<int>|
                indices.len() == k as int
                && forall |a: int| 0 <= a < indices.len() ==>
                    0 <= #[trigger] indices[a] < result@.len() - 1
                && forall |a: int, b: int|
                    0 <= a < b < indices.len() ==>
                    #[trigger] Self::adj_diff(result@, indices[a]) != #[trigger] Self::adj_diff(result@, indices[b])
                && forall |j: int| 0 <= j < result@.len() - 1 ==>
                    exists |a: int| 0 <= a < indices.len()
                    && #[trigger] Self::adj_diff(result@, j) == Self::adj_diff(result@, indices[a]),
    {
    }
}

}
