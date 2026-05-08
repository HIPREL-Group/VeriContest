use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cost_to_reach(a: Seq<i64>, mid: int, target: int) -> int
        decreases a.len() - mid,
    {
        if mid >= a.len() {
            0int
        } else {
            let diff = if target > a[mid] { target - a[mid] } else { 0int };
            diff + Self::cost_to_reach(a, mid + 1, target)
        }
    }

    pub open spec fn spec_is_achievable(a: Seq<i64>, n: int, k: int, target: int) -> bool {
        Self::cost_to_reach(a, n / 2, target) <= k
    }

    pub open spec fn spec_sorted(a: Seq<i64>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
    }

    pub fn max_median(n: usize, k: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= n <= 200000,
            n % 2 == 1,
            a.len() == n,
            1 <= k <= 1000000000,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= 1000000000,
            Self::spec_sorted(a@),
        ensures
            forall|v: int| v <= res as int ==> Self::spec_is_achievable(a@, n as int, k as int, v),
            forall|v: int| v > res as int ==> !Self::spec_is_achievable(a@, n as int, k as int, v),
    {
    }
}

}
