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
            invariant
                n == arr.len(),
                2 <= arr.len() <= 500,
                forall |k: int| 0 <= k < arr.len() ==> -1000 <= #[trigger] arr[k] <= 1000,
                0 <= i <= n,
                forall |k: int, m: int| 0 <= k < i && 0 <= m < arr.len() && k != m ==> arr[k] != 2 * arr[m],
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    n == arr.len(),
                    2 <= arr.len() <= 500,
                    forall |k: int| 0 <= k < arr.len() ==> -1000 <= #[trigger] arr[k] <= 1000,
                    0 <= i < n,
                    0 <= j <= n,
                    forall |k: int, m: int| 0 <= k < i && 0 <= m < arr.len() && k != m ==> arr[k] != 2 * arr[m],
                    forall |m: int| 0 <= m < j && (i as int) != m ==> arr[i as int] != 2 * arr[m],
                decreases n - j,
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
