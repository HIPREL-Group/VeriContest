use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alt_at(arr: Seq<i32>, i: int) -> bool {
        2 <= i < arr.len()
        && ((arr[i - 2] < arr[i - 1] && arr[i - 1] > arr[i])
            || (arr[i - 2] > arr[i - 1] && arr[i - 1] < arr[i]))
    }

    pub open spec fn is_turbulent(arr: Seq<i32>, start: int, end: int) -> bool {
        0 <= start <= end < arr.len()
        && (forall |k: int| start < k <= end ==> #[trigger] arr[k - 1] != arr[k])
        && (forall |k: int| start + 2 <= k <= end ==> #[trigger] Self::alt_at(arr, k))
    }

    pub open spec fn turbulent_len(arr: Seq<i32>, start: int, len: int) -> bool {
        1 <= len
        && start + len <= arr.len()
        && Self::is_turbulent(arr, start, start + len - 1)
    }

    pub open spec fn run_at(arr: Seq<i32>, i: int) -> nat
        decreases i
    {
        if i <= 0 {
            1
        } else if i == 1 {
            if arr[0] != arr[1] { 2 } else { 1 }
        } else if Self::alt_at(arr, i) {
            Self::run_at(arr, i - 1) + 1
        } else if arr[i - 1] != arr[i] {
            2
        } else {
            1
        }
    }

    pub open spec fn max_run(arr: Seq<i32>, i: int) -> nat
        decreases i
    {
        if i <= 0 {
            1
        } else {
            let prev = Self::max_run(arr, i - 1);
            let cur = Self::run_at(arr, i);
            if cur > prev { cur } else { prev }
        }
    }

    pub fn max_turbulence_size(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 40_000,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
        ensures
            1 <= result,
            result as int <= arr.len(),
            exists |start: int|
                0 <= start && start + result <= arr.len()
                && #[trigger] Self::turbulent_len(arr@, start, result as int),
            forall |start: int, len: int|
                0 <= start && 1 <= len && start + len <= arr.len() as int && len > result as int
                ==> !#[trigger] Self::turbulent_len(arr@, start, len),
    {
    }
}

}
