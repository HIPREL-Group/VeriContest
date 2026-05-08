use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_merge_value(nums: Seq<i32>, start: int) -> int
        decreases nums.len() - start,
    {
        if start + 1 >= nums.len() {
            nums[start] as int
        } else {
            let right = Self::suffix_merge_value(nums, start + 1);
            if nums[start] as int <= right {
                nums[start] as int + right
            } else {
                nums[start] as int
            }
        }
    }

    pub fn max_array_value(nums: Vec<i32>) -> (ans: i64)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
        ensures
            ans as int == Self::suffix_merge_value(nums@, 0),
    {
        let n = nums.len() as i32;
        let mut cur: i64 = nums[(n - 1) as usize] as i64;
        let mut i: i32 = n - 2;
        while i >= 0
            invariant
                1 <= n <= 100000,
                n == nums.len() as i32,
                -1 <= i <= n - 2,
                cur as int == Self::suffix_merge_value(nums@, (i + 1) as int),
                1 <= cur as int <= 1000000 * (n as int - (i + 1) as int),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000,
            decreases i + 1,
        {
            if nums[i as usize] as i64 <= cur {
                proof {
                    assert(1 <= nums@[i as int] <= 1000000);
                    assert(cur as int + nums@[i as int] as int <= 1000000 * (n as int - i as int)) by (nonlinear_arith)
                        requires
                            cur as int <= 1000000 * (n as int - (i + 1) as int),
                            nums@[i as int] as int <= 1000000;
                }
                cur = cur + nums[i as usize] as i64;
            } else {
                cur = nums[i as usize] as i64;
            }
            i = i - 1;
        }
        cur
    }
}

}
