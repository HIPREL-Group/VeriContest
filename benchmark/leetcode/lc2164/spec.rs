use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn even_indices_sorted_between(s: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| 0 <= i < j < s.len() && from <= i && j < to && i % 2 == 0 && j % 2 == 0 ==> s[i] <= s[j]
    }

    pub open spec fn odd_indices_sorted_between(s: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| 0 <= i < j < s.len() && from <= i && j < to && i % 2 == 1 && j % 2 == 1 ==> s[i] >= s[j]
    }

    pub open spec fn even_indices_sorted(s: Seq<i32>) -> bool {
        Self::even_indices_sorted_between(s, 0, s.len() as int)
    }

    pub open spec fn odd_indices_sorted(s: Seq<i32>) -> bool {
        Self::odd_indices_sorted_between(s, 0, s.len() as int)
    }

    pub fn sort_even_odd(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            Self::even_indices_sorted(result@),
            Self::odd_indices_sorted(result@),
            exists |r: Seq<int>| Self::is_reorder_of(r, result@, nums@),
    {
    }
}

}