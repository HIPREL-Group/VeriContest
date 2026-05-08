use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_u64(a: u64, b: u64) -> u64 {
        if a <= b { a } else { b }
    }

    pub open spec fn prefix_min_u64(nums: Seq<i32>, end: int) -> u64
        decreases end,
    {
        if end <= 1 {
            nums[0] as u64
        } else {
            Self::min_u64(Self::prefix_min_u64(nums, end - 1), nums[end - 1] as u64)
        }
    }

    pub open spec fn prefix_count_eq_u64(nums: Seq<i32>, end: int, v: u64) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_count_eq_u64(nums, end - 1, v)
                + if nums[end - 1] as u64 == v { 1int } else { 0int }
        }
    }

    pub open spec fn all_divisible_u64(nums: Seq<i32>, m: u64) -> bool {
        forall |k: int| 0 <= k < nums.len() ==> (nums[k] as u64) % m == 0u64
    }

    pub open spec fn minimum_array_length_spec(nums: Seq<i32>) -> int {
        let m = Self::prefix_min_u64(nums, nums.len() as int);
        if !Self::all_divisible_u64(nums, m) {
            1
        } else {
            (Self::prefix_count_eq_u64(nums, nums.len() as int, m) + 1) / 2
        }
    }

    pub fn minimum_array_length(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result as int == Self::minimum_array_length_spec(nums@),
    {
        let n = nums.len();
        let mut min_v = nums[0] as u64;
        let mut i: usize = 1;
        while i < n {
            let x = nums[i] as u64;
            if x < min_v {
                min_v = x;
            }
            i += 1;
        }

        i = 0;
        while i < n {
            let x = nums[i] as u64;
            if x % min_v != 0 {
                return 1;
            }
            i += 1;
        }

        let mut cnt_min: i32 = 0;
        i = 0;
        while i < n {
            if nums[i] as u64 == min_v {
                cnt_min += 1;
            }
            i += 1;
        }
        (cnt_min + 1) / 2
    }
}

}
