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
        let n = arr.len();
        let mut i: usize = 0;
        while i + 2 < n
            invariant
                n == arr.len(),
                1 <= arr.len() <= 1000,
                i <= n,
                forall |k: int| 0 <= k < arr.len() ==> 1 <= #[trigger] arr[k] <= 1000,
                forall |j: int| 0 <= j < i && j + 2 < arr.len() ==> !(#[trigger] arr[j] % 2 == 1 && arr[j + 1] % 2 == 1 && arr[j + 2] % 2 == 1),
            decreases n - i,
        {
            if arr[i] % 2 == 1 && arr[i + 1] % 2 == 1 && arr[i + 2] % 2 == 1 {
                return true;
            }
            i = i + 1;
        }
        false
    }
}

}
