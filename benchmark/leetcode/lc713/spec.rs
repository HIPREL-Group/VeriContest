use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn segment_product(nums: Seq<i32>, i: int, j: int) -> int
        decreases j - i,
    {
        if i > j {
            1
        } else if i == j {
            nums[i] as int
        } else {
            (nums[i] as int) * Self::segment_product(nums, i + 1, j)
        }
    }

    pub open spec fn count_product_less(nums: Seq<i32>, k: int, i: int, n: int) -> int
        decreases n - i,
    {
        if i >= n {
            0
        } else {
            Self::num_ends(nums, k, i, i, n) + Self::count_product_less(nums, k, i + 1, n)
        }
    }

    pub open spec fn num_ends(nums: Seq<i32>, k: int, i: int, j: int, n: int) -> int
        decreases n - j,
    {
        if j >= n {
            0
        } else if Self::segment_product(nums, i, j) < k {
            1 + Self::num_ends(nums, k, i, j + 1, n)
        } else {
            0
        }
    }

    pub fn num_subarray_product_less_than_k(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 30_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            0 <= k <= 1_000_000,
        ensures
            res >= 0,
            res as int == Self::count_product_less(nums@, k as int, 0, nums.len() as int),
    {
    }
}

}
