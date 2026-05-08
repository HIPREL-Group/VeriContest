use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(nums: Seq<i32>, i: nat, cur: nat, total: nat) -> nat
        recommends
            i <= nums.len(),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            total
        } else {
            let cur2 = if nums[i as int] == 0 { cur + 1 } else { 0 };
            let total2 = total + cur2;
            Self::scan_spec(nums, i + 1, cur2, total2)
        }
    }

    pub open spec fn zero_filled_subarray_spec(nums: Seq<i32>) -> nat {
        Self::scan_spec(nums, 0, 0, 0)
    }

    pub fn zero_filled_subarray(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            0 <= result,
            result as nat == Self::zero_filled_subarray_spec(nums@),
    {
        let mut i: usize = 0;
        let mut cur: i128 = 0;
        let mut total: i128 = 0;

        while i < nums.len() {
            let x = nums[i];
            if x == 0 {
                cur = cur + 1;
                total = total + cur;
            } else {
                cur = 0;
            }
            i = i + 1;
        }

        total as i64
    }
}

}
