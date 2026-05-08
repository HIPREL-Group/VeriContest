use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min_or_after_operations(nums: Seq<i32>, k: int) -> int {
        0
    }

    pub fn min_or_after_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            0 <= k < nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
        ensures
            result as int == Self::spec_min_or_after_operations(nums@, k as int),
    {
        let all: i32 = 1_073_741_823;
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut bit: i32 = 29;
        let mut bit_val: i32 = 536_870_912;

        while bit >= 0 {
            let target = ans | (bit_val - 1);
            let mut cnt: i32 = 0;
            let mut cur: i32 = all;
            let mut idx: usize = 0;

            while idx < n {
                cur = cur & nums[idx];
                if (cur | target) == target {
                    cur = all;
                } else {
                    cnt = cnt + 1;
                }
                idx = idx + 1;
            }

            if cnt > k {
                ans = ans | bit_val;
            }

            bit = bit - 1;
            if bit_val > 0 {
                bit_val = bit_val / 2;
            }
        }

        ans
    }
}

}
