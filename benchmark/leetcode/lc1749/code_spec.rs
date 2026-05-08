use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(s: Seq<i32>, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            s[k - 1] as int + Self::prefix_sum(s, k - 1)
        }
    }

    pub open spec fn subarray_sum(s: Seq<i32>, l: int, r: int) -> int {
        Self::prefix_sum(s, r + 1) - Self::prefix_sum(s, l)
    }

    pub fn max_absolute_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100000,
            forall|i: int| 0 <= i < nums@.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
        ensures
            result >= 0,
            forall|l: int, r: int|
                0 <= l <= r < nums@.len() ==>
                    result as int >= #[trigger] Self::subarray_sum(nums@, l, r)
                        && result as int >= -Self::subarray_sum(nums@, l, r),
            result == 0 || exists|l: int, r: int|
                0 <= l && l <= r && r < nums@.len()
                    && (result as int == Self::subarray_sum(nums@, l, r)
                        || result as int == -Self::subarray_sum(nums@, l, r)),
    {
        let n = nums.len();
        let mut s: i32 = 0;
        let mut max_prefix: i32 = 0;
        let mut min_prefix: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            s = s + nums[i];
            if s > max_prefix {
                max_prefix = s;
            }
            if s < min_prefix {
                min_prefix = s;
            }
            i = i + 1;
        }
        max_prefix - min_prefix
    }
}

}
