use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn can_jump_to(arr: Seq<i32>, d: int, from: int, to: int) -> bool {
    let lo = if from < to { from } else { to };
    let hi = if from < to { to } else { from };
    0 <= from < arr.len() as int
    && 0 <= to < arr.len() as int
    && from != to
    && hi - lo <= d
    && arr[from] > arr[to]
    && forall|k: int| lo < k < hi ==> arr[from] > arr[k]
}

pub open spec fn is_valid_path(arr: Seq<i32>, d: int, path: Seq<int>) -> bool {
    path.len() >= 1
    && (forall|i: int| 0 <= i < path.len() ==> 0 <= (#[trigger] path[i]) < arr.len())
    && (forall|i: int| 0 <= i < path.len() - 1 ==>
        can_jump_to(arr, d, (#[trigger] path[i]), path[i + 1]))
}

pub open spec fn has_path_of_length(arr: Seq<i32>, d: int, len: int) -> bool {
    exists|path: Seq<int>| path.len() == len && (#[trigger] is_valid_path(arr, d, path))
}

impl Solution {
    pub fn max_jumps(arr: Vec<i32>, d: i32) -> (result: i32)
        requires
            1 <= arr.len() <= 1000,
            1 <= d <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> 1 <= (#[trigger] arr[i]) <= 100_000,
        ensures
            1 <= result <= arr@.len() as i32,
            has_path_of_length(arr@, d as int, result as int),
            forall|k: int| k > result as int ==> !has_path_of_length(arr@, d as int, k),
    {
    }
}

}
