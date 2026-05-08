use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_valid_decrements(n: usize, a: Seq<i32>, b: Seq<i32>, max_diff: i32) -> bool {
    (forall|i: int| 0 <= i && i < n ==> a[i] >= b[i]) &&
    (forall|i: int| 0 <= i && i < n ==> a[i] - b[i] <= max_diff) &&
    (forall|i: int| 0 <= i && i < n ==>
        (a[i] - b[i] == max_diff || b[i] == 0))
}

pub open spec fn has_valid_decrements(n: usize, a: Seq<i32>, b: Seq<i32>) -> bool {
    exists|max_diff: i32| max_diff >= 0 && is_valid_decrements(n, a, b, max_diff)
}

pub struct Solution;

impl Solution {
    pub fn is_possible(n: usize, a: Vec<i32>, b: Vec<i32>) -> (res: bool)
        requires
            1 <= n && n <= 50000,
            a.len() == n,
            b.len() == n,
            forall|i: int| 0 <= i && i < n ==> 0 <= a@[i] && a@[i] <= 1000000000,
            forall|i: int| 0 <= i && i < n ==> 0 <= b@[i] && b@[i] <= 1000000000,
        ensures
            res == has_valid_decrements(n, a@, b@)
    {
    }
}

}
