use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_in_arr(arr: Seq<i32>, val: int) -> bool {
        exists |i: int| 0 <= i < arr.len() && arr[i] as int == val
    }

    pub open spec fn count_missing_up_to(arr: Seq<i32>, val: int) -> int
        decreases val
    {
        if val <= 0 { 0 }
        else {
            (if !Self::is_in_arr(arr, val) { 1int } else { 0int })
            + Self::count_missing_up_to(arr, val - 1)
        }
    }

    pub fn find_kth_positive(arr: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= arr.len() <= 1000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
            1 <= k <= 1000,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j],
        ensures
            result >= 1,
            !Self::is_in_arr(arr@, result as int),
            Self::count_missing_up_to(arr@, result as int) == k as int,
    {
        let mut missing: i32 = 0;
        let mut current: i32 = 1;
        let mut idx: usize = 0;

        while missing < k
        {
            if idx < arr.len() && arr[idx] == current {
                idx = idx + 1;
            } else {
                missing = missing + 1;
            }
            current = current + 1;
        }

        current - 1
    }
}

}
