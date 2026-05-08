use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn triple_product(nums: Seq<i32>, i: int, j: int, k: int) -> int
        recommends
            0 <= i < j < k < nums.len(),
    {
        nums[i] as int * nums[j] as int * nums[k] as int
    }

    pub fn maximum_product(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() >= 3,
            forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            exists|i: int, j: int, k: int|
                0 <= i < j < k < nums.len()
                && result as int == #[trigger] Self::triple_product(nums@, i, j, k),
            forall|i: int, j: int, k: int|
                0 <= i < j < k < nums.len()
                ==> #[trigger] Self::triple_product(nums@, i, j, k) <= result as int,
    {
    }
}

}
