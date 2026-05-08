use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn inner_sum(nums: Seq<i32>, i: int, end_j: int) -> int
    decreases end_j,
{
    if end_j <= 0 {
        0
    } else {
        inner_sum(nums, i, end_j - 1) + (nums[i] as int) / (nums[end_j - 1] as int)
    }
}

pub open spec fn outer_sum(nums: Seq<i32>, end_i: int) -> int
    decreases end_i,
{
    if end_i <= 0 {
        0
    } else {
        outer_sum(nums, end_i - 1) + inner_sum(nums, end_i - 1, nums.len() as int)
    }
}








impl Solution {
    pub fn sum_of_floored_pairs(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result as int == outer_sum(nums@, nums.len() as int) % 1_000_000_007,
    {
        let n = nums.len();
        let modulo: i64 = 1_000_000_007;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                let div_val = (nums[i] as i64) / (nums[j] as i64);
                sum = (sum + div_val) % modulo;
                j = j + 1;
            }
            i = i + 1;
        }
        (sum % modulo) as i32
    }
}

}
