use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn xor_range(arr: Seq<i32>, start: int, end: int) -> i32
    decreases end - start
{
    if start >= end {
        0i32
    } else {
        xor_range(arr, start, end - 1) ^ arr[end - 1]
    }
}

pub open spec fn count_k(arr: Seq<i32>, i: int, k: int) -> int
    decreases arr.len() - k
{
    if k >= arr.len() {
        0
    } else {
        (if xor_range(arr, i, k + 1) == 0i32 { k - i } else { 0int })
        + count_k(arr, i, k + 1)
    }
}

pub open spec fn count_all(arr: Seq<i32>, i: int) -> int
    decreases arr.len() - i
{
    if i >= arr.len() {
        0
    } else {
        count_k(arr, i, i + 1) + count_all(arr, i + 1)
    }
}

impl Solution {
    pub fn count_triplets(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 300,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000_000,
        ensures
            res as int == count_all(arr@, 0),
    {
    }
}

}
