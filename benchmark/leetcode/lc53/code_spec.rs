use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_range(s: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= s.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            s[l] as int + Self::sum_range(s, l + 1, r)
        }
    }

    pub fn max_sub_array(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
        ensures
            exists |l: int, r: int|
                0 <= l < r <= nums.len() as int &&
                result as int == #[trigger] Self::sum_range(nums@, l, r),
            forall |l: int, r: int|
                0 <= l < r <= nums.len() as int ==>
                #[trigger] Self::sum_range(nums@, l, r) <= result as int,
    {
        let n = nums.len();

        let mut max_here: i64 = nums[0] as i64;
        let mut max_so_far: i64 = nums[0] as i64;

        let mut i: usize = 1;

        while i < n
        {
            let old_max_here: i64 = max_here;
            let candidate: i64 = old_max_here + nums[i] as i64;
            let old_max_so_far: i64 = max_so_far;

            if candidate >= nums[i] as i64 {
                max_here = candidate;
            } else {
                max_here = nums[i] as i64;
            }
            if max_here > max_so_far {
                max_so_far = max_here;
            }

            i += 1;
        }

        max_so_far as i32
    }
}

} 
