use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subarray_sum(s: Seq<i32>, i: int, j: int) -> int
    decreases j - i + 1,
{
    if i > j { 0 }
    else { subarray_sum(s, i, j - 1) + s[j] as int }
}

pub open spec fn count_odd_ending(s: Seq<i32>, end_idx: int, k: int) -> int
    decreases k + 1,
{
    if k < 0 { 0 }
    else {
        count_odd_ending(s, end_idx, k - 1)
        + if subarray_sum(s, k, end_idx) % 2 != 0 { 1 as int } else { 0 as int }
    }
}

pub open spec fn count_odd_subarrays(s: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else {
        count_odd_subarrays(s, n - 1) + count_odd_ending(s, n - 1, n - 1)
    }
}

impl Solution {
    pub fn num_of_subarrays(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
        ensures
            0 <= res < 1_000_000_007,
            res as int == count_odd_subarrays(arr@, arr.len() as int) % 1_000_000_007,
    {
    }
}

}
