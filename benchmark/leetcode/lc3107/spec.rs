use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn op_cost_at(v: int, idx: int, mid: int, k: int) -> int {
        if idx < mid {
            if v > k { v - k } else { 0 }
        } else if idx == mid {
            if v >= k { v - k } else { k - v }
        } else {
            if v < k { k - v } else { 0 }
        }
    }

    pub open spec fn cost_prefix(s: Seq<i32>, k: int, mid: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n > s.len() {
            Self::cost_prefix(s, k, mid, s.len() as int)
        } else {
            Self::cost_prefix(s, k, mid, n - 1)
                + Self::op_cost_at(s[n - 1] as int, n - 1, mid, k)
        }
    }

    pub open spec fn cost_all(s: Seq<i32>, k: int) -> int {
        Self::cost_prefix(s, k, (s.len() / 2) as int, s.len() as int)
    }

    pub fn min_operations_to_make_median_k(nums: Vec<i32>, k: i32) -> (result: i64)
        requires
            1 <= nums.len() <= 200000,
            1 <= k <= 1000000000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, nums@)
                && result as int == Self::cost_all(s, k as int),
    {
    }
}

}
