use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn three_consecutive_odds(arr: Vec<i32>) -> (result: bool)
        requires
            1 <= arr.len() <= 1000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
        ensures
            result == (exists |i: int| 0 <= i && i + 2 < arr.len() && #[trigger] arr[i] % 2 == 1 && arr[i + 1] % 2 == 1 && arr[i + 2] % 2 == 1),
    {
    }
}

}
