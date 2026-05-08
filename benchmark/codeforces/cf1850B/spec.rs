use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid(a: Seq<u32>, idx: int) -> bool {
    0 <= idx < a.len() && a[idx] <= 10
}

impl Solution {
    pub fn find_winner(a: Vec<u32>, b: Vec<u32>, n: usize) -> (result: usize)
        requires
            1 <= n <= 50,
            a.len() == n,
            b.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 50,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 50,
            exists|i: int| 0 <= i < a.len() && #[trigger] a[i] <= 10,
        ensures
            1 <= result <= n,
            a[result as int - 1] <= 10,
            forall|j: int| 0 <= j < n && #[trigger] a[j] <= 10 ==> b[j] <= b[result as int - 1],
    {
    }
}

}
