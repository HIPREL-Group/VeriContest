use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_min_distance(nums: Vec<i32>, target: i32, start: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
            0 <= start < nums.len(),
            exists |i: int| 0 <= i < nums.len() && #[trigger] nums[i] == target,
        ensures
            0 <= result < nums.len(),
            exists |i: int| 0 <= i < nums.len() && #[trigger] nums[i] == target && result == if i >= start { i - start } else { start - i },
            forall |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == target ==>
                result <= if j >= start { j - start } else { start - j },
    {
        let n: usize = nums.len();
        let mut min_dist: i32 = n as i32;
        let mut i: usize = 0;
        
        while i < n {
            if nums[i] == target {
                let dist = if (i as i32) > start {
                    (i as i32) - start
                } else {
                    start - (i as i32)
                };
                if dist < min_dist {
                    min_dist = dist;
                }
            }
            i = i + 1;
        }
        
        min_dist
    }
}

}
