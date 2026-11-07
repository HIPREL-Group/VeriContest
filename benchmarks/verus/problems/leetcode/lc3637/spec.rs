use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inc_prefix(nums: Seq<i32>, p: int) -> bool {
        0 < p && p < nums.len()
        && forall|j: int| 0 <= j && j < p ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn dec_mid(nums: Seq<i32>, p: int, q: int) -> bool {
        0 < p && p < q && q < nums.len()
        && forall|j: int| p <= j && j < q ==> #[trigger] nums[j] > nums[j + 1]
    }

    pub open spec fn inc_suffix(nums: Seq<i32>, q: int) -> bool {
        0 <= q && q < nums.len() - 1
        && forall|j: int| q <= j && j < nums.len() - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn trionic_at(nums: Seq<i32>, p: int, q: int) -> bool {
        0 < p && p < q && q < nums.len() - 1
        && Self::inc_prefix(nums, p)
        && Self::dec_mid(nums, p, q)
        && Self::inc_suffix(nums, q)
    }

    pub open spec fn has_trionic(nums: Seq<i32>) -> bool {
        exists|p: int, q: int| #[trigger] Self::trionic_at(nums, p, q)
    }

    pub fn is_trionic(nums: Vec<i32>) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::has_trionic(nums@),
    {
    }
}

}
