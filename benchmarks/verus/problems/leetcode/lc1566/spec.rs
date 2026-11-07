use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn elem_match(arr: Seq<i32>, start: int, m: int, i: int) -> bool {
    arr[start + i] == arr[start + m + i]
}

pub open spec fn has_pattern(arr: Seq<i32>, start: int, m: int, k: int) -> bool {
    forall |i: int| 0 <= i < (k - 1) * m ==> #[trigger] elem_match(arr, start, m, i)
}

impl Solution {
    pub fn contains_pattern(arr: Vec<i32>, m: i32, k: i32) -> (res: bool)
        requires
            2 <= arr.len() <= 100,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
            1 <= m <= 100,
            2 <= k <= 100,
        ensures
            res == exists |start: int| 0 <= start && start + (k as int) * (m as int) <= arr.len() && has_pattern(arr@, start, m as int, k as int),
    {
    }
}

}
