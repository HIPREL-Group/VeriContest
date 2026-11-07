use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn maximum_difference(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            res == -1 || res >= 1,
            res == -1 ==>
                forall |a: int, b: int| 0 <= a < b < nums.len() as int
                    ==> nums[a] >= nums[b],
            res >= 1 ==>
                exists |a: int, b: int| 0 <= a < b < nums.len() as int
                    && nums[a] < nums[b]
                    && res == nums[b] - nums[a],
            res >= 1 ==>
                forall |a: int, b: int| 0 <= a < b < nums.len() as int
                    && nums[a] < nums[b]
                    ==> nums[b] - nums[a] <= res,
    {
        let n = nums.len();
        let mut min_val: i64 = nums[0] as i64;
        let mut best: i64 = -1;
        let mut i: usize = 1;

        while i < n
        {
            if nums[i] as i64 > min_val {
                let diff = nums[i] as i64 - min_val;
                if diff > best {
                    best = diff;
                }
            }
            if (nums[i] as i64) < min_val {
                min_val = nums[i] as i64;
            }
            i += 1;
        }

        best as i32
    }
}

} 
