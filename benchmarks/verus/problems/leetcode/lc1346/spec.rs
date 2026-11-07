use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn check_if_exist(arr: Vec<i32>) -> (res: bool)
        requires
            2 <= arr.len() <= 500,
            forall |k: int| 0 <= k < arr.len() ==> -1000 <= #[trigger] arr[k] <= 1000,
        ensures
            res == (exists |i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j && arr[i] == 2 * arr[j]),
    {
        
    }
}

}
