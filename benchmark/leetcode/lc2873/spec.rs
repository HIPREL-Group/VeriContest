use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn triplet_value(nums: Seq<i32>, i: int, j: int, k: int) -> int
        recommends
            0 <= i < j < k < nums.len(),
    {
        (nums[i] as int - nums[j] as int) * nums[k] as int
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn max_k(nums: Seq<i32>, i: int, j: int, k: int, acc: int) -> int
        decreases nums.len() - k,
    {
        if k >= nums.len() {
            acc
        } else {
            let v = Self::triplet_value(nums, i, j, k);
            Self::max_k(nums, i, j, k + 1, Self::max2(acc, v))
        }
    }

    pub open spec fn max_j(nums: Seq<i32>, i: int, j: int, acc: int) -> int
        decreases nums.len() - j,
    {
        if j >= nums.len() {
            acc
        } else {
            let acc2 = Self::max_k(nums, i, j, j + 1, acc);
            Self::max_j(nums, i, j + 1, acc2)
        }
    }

    pub open spec fn max_i(nums: Seq<i32>, i: int, acc: int) -> int
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            acc
        } else {
            let acc2 = Self::max_j(nums, i, i + 1, acc);
            Self::max_i(nums, i + 1, acc2)
        }
    }

    pub open spec fn maximum_triplet_value_spec(nums: Seq<i32>) -> int {
        Self::max_i(nums, 0, 0)
    }

    pub fn maximum_triplet_value(nums: Vec<i32>) -> (result: i64)
        requires
            3 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            result as int == Self::maximum_triplet_value_spec(nums@),
    {
    }
}

}
