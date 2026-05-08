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
        let n = arr.len();
        let mut i: usize = 0;
        while i < n
        {
            let mut j: usize = 0;
            while j < n
            {
                if i != j && arr[i] == 2 * arr[j] {
                    return true;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        false
    }
}

}
