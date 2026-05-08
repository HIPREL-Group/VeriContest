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

    fn solve_k(nums: &Vec<i32>, i: usize, j: usize, k: usize, acc: i64) -> (res: i64)
        requires
            i < j,
            j < nums.len(),
            j <= k,
            k <= nums.len(),
            forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] <= 1_000_000,
            -9_223_372_036_854_775_808 <= acc <= 9_223_372_036_854_775_807,
        ensures
            res as int == Self::max_k(nums@, i as int, j as int, k as int, acc as int),
        decreases nums.len() - k,
    {
        if k >= nums.len() {
            acc
        } else {
            proof {
                assert(0 <= nums[i as int] <= 1_000_000);
                assert(0 <= nums[j as int] <= 1_000_000);
                assert(0 <= nums[k as int] <= 1_000_000);
                assert(-1_000_000 <= nums[i as int] - nums[j as int] <= 1_000_000);
                assert(-1_000_000_000_000 <= (nums[i as int] - nums[j as int]) * nums[k as int] <= 1_000_000_000_000) by (nonlinear_arith)
                    requires
                        -1_000_000 <= nums[i as int] - nums[j as int] <= 1_000_000,
                        0 <= nums[k as int] <= 1_000_000;
            }
            let v: i64 = (nums[i] as i64 - nums[j] as i64) * nums[k] as i64;
            let acc2: i64 = if acc >= v { acc } else { v };
            proof {
                assert(v as int == Self::triplet_value(nums@, i as int, j as int, k as int));
                assert(acc2 as int == Self::max2(acc as int, v as int));
            }
            Self::solve_k(nums, i, j, k + 1, acc2)
        }
    }

    fn solve_j(nums: &Vec<i32>, i: usize, j: usize, acc: i64) -> (res: i64)
        requires
            i < j,
            i < nums.len(),
            j <= nums.len(),
            forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] <= 1_000_000,
            -9_223_372_036_854_775_808 <= acc <= 9_223_372_036_854_775_807,
        ensures
            res as int == Self::max_j(nums@, i as int, j as int, acc as int),
        decreases nums.len() - j,
    {
        if j >= nums.len() {
            acc
        } else {
            let acc2: i64 = Self::solve_k(nums, i, j, j + 1, acc);
            Self::solve_j(nums, i, j + 1, acc2)
        }
    }

    fn solve_i(nums: &Vec<i32>, i: usize, acc: i64) -> (res: i64)
        requires
            i <= nums.len(),
            forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] <= 1_000_000,
            -9_223_372_036_854_775_808 <= acc <= 9_223_372_036_854_775_807,
        ensures
            res as int == Self::max_i(nums@, i as int, acc as int),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            acc
        } else {
            let acc2: i64 = Self::solve_j(nums, i, i + 1, acc);
            Self::solve_i(nums, i + 1, acc2)
        }
    }

    pub fn maximum_triplet_value(nums: Vec<i32>) -> (result: i64)
        requires
            3 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            result as int == Self::maximum_triplet_value_spec(nums@),
    {
        Self::solve_i(&nums, 0, 0)
    }
}

}
