use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_val(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn is_good_triplet(arr: Seq<i32>, i: int, j: int, k: int, a: int, b: int, c: int) -> bool {
        0 <= i < j && j < k && k < arr.len() &&
        Self::abs_val(arr[i] as int - arr[j] as int) <= a &&
        Self::abs_val(arr[j] as int - arr[k] as int) <= b &&
        Self::abs_val(arr[i] as int - arr[k] as int) <= c
    }

    pub open spec fn count_i_spec(arr: Seq<i32>, a: int, b: int, c: int, j: int, k: int, i_bound: int) -> int
        decreases i_bound,
    {
        if i_bound <= 0 { 0 }
        else {
            Self::count_i_spec(arr, a, b, c, j, k, i_bound - 1) +
            if Self::is_good_triplet(arr, i_bound - 1, j, k, a, b, c) { 1int } else { 0int }
        }
    }

    pub open spec fn count_j_spec(arr: Seq<i32>, a: int, b: int, c: int, k: int, j_bound: int) -> int
        decreases j_bound,
    {
        if j_bound <= 1 { 0 }
        else {
            Self::count_j_spec(arr, a, b, c, k, j_bound - 1) +
            Self::count_i_spec(arr, a, b, c, j_bound - 1, k, j_bound - 1)
        }
    }

    pub open spec fn count_k_spec(arr: Seq<i32>, a: int, b: int, c: int, k_bound: int) -> int
        decreases k_bound,
    {
        if k_bound <= 2 { 0 }
        else {
            Self::count_k_spec(arr, a, b, c, k_bound - 1) +
            Self::count_j_spec(arr, a, b, c, k_bound - 1, k_bound - 1)
        }
    }

    pub fn count_good_triplets(arr: Vec<i32>, a: i32, b: i32, c: i32) -> (result: i32)
        requires
            3 <= arr.len() <= 100,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1000,
            0 <= a <= 1000,
            0 <= b <= 1000,
            0 <= c <= 1000,
        ensures
            result as int == Self::count_k_spec(arr@, a as int, b as int, c as int, arr.len() as int),
    {
    }
}

}
