use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_contains(nums: Seq<i32>, x: i32) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] == x
    }

    pub open spec fn strictly_increasing(nums: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j]
    }

    pub open spec fn is_lower_bound(nums: Seq<i32>, lo: i32) -> bool {
        Self::seq_contains(nums, lo)
            && forall |i: int| 0 <= i < nums.len() ==> lo <= nums[i]
    }

    pub open spec fn is_upper_bound(nums: Seq<i32>, hi: i32) -> bool {
        Self::seq_contains(nums, hi)
            && forall |i: int| 0 <= i < nums.len() ==> nums[i] <= hi
    }

    pub fn find_missing_elements(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            exists |lo: i32, hi: i32|
                Self::is_lower_bound(nums@, lo)
                && Self::is_upper_bound(nums@, hi)
                && forall |i: int|
                    0 <= i < result.len() ==> lo < #[trigger] result@[i] < hi && !Self::seq_contains(nums@, result@[i])
                && forall |x: i32|
                    lo < x < hi && !Self::seq_contains(nums@, x) ==> #[trigger] Self::seq_contains(result@, x)
                && Self::strictly_increasing(result@),
    {
    }
}

} 
