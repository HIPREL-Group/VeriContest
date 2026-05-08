use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_spy(a: Seq<i64>, i: int) -> bool {
    &&& 0 <= i < a.len()
    &&& forall|j: int| 0 <= j < a.len() && j != i ==> a[j] != a[i]
    &&& forall|j: int, k: int| 0 <= j < a.len() && 0 <= k < a.len() && j != i && k != i ==> a[j] == a[k]
}

impl Solution {
    pub fn spy_index(a: Vec<i64>) -> (res: usize)
        requires
            3 <= a.len() <= 100,
            exists|i: int| is_spy(a@, i),
        ensures
            is_spy(a@, res as int - 1),
    {
    }
}

}
