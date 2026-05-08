use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_good(nums: Seq<i32>, k: int, i: int) -> bool {
    (if i < k {
        true
    } else {
        nums[i] > nums[i - k]
    }) && (if i + k >= nums.len() {
        true
    } else {
        nums[i] > nums[i + k]
    })
}

pub open spec fn spec_sum_good_prefix(nums: Seq<i32>, k: int, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        spec_sum_good_prefix(nums, k, end - 1)
            + (if is_good(nums, k, end - 1) {
                nums[end - 1] as int
            } else {
                0
            })
    }
}

impl Solution {
    pub fn sum_of_good_numbers(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            1 <= k,
            k as int <= nums.len() as int / 2,
        ensures
            result as int == spec_sum_good_prefix(nums@, k as int, nums.len() as int),
    {
        let n = nums.len();
        let kk: usize = k as usize;
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let left_ok: bool;
            if i >= kk {
                left_ok = nums[i] > nums[i - kk];
            } else {
                left_ok = true;
            }

            let right_ok: bool;
            if kk < n - i {
                right_ok = nums[i] > nums[i + kk];
            } else {
                right_ok = true;
            }

            let mut add: i32 = 0;
            if left_ok && right_ok {
                add = nums[i];
            }
            sum = sum + add;
            i = i + 1;
        }
        sum
    }
}

}
