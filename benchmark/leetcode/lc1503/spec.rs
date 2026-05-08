use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_last_moment(n: i32, left: Vec<i32>, right: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 10_000,
            left.len() + right.len() >= 1,
            left.len() + right.len() <= n + 1,
            forall |i: int| 0 <= i < left.len() ==> 0 <= #[trigger] left[i] <= n,
            forall |i: int| 0 <= i < right.len() ==> 0 <= #[trigger] right[i] <= n,
        ensures
            0 <= res <= n,
            forall |i: int| 0 <= i < left.len() ==> res >= #[trigger] left[i],
            forall |i: int| 0 <= i < right.len() ==> res >= n - #[trigger] right[i],
            (exists |k: int| 0 <= k < left.len() && res == left[k])
            || (exists |k: int| 0 <= k < right.len() && res == n - right[k]),
    {
    }
}

}
