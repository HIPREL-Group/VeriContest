use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_values_in_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            0
        } else {
            let has_value = exists |i: int| 0 <= i < nums.len() && nums[i] == start;
            (if has_value { 1 as int } else { 0 as int }) + Self::count_values_in_range(nums, start + 1, end)
        }
    }

    pub fn minimum_operations(nums: Vec<i32>) -> (res: i32) 
        requires 
            1 <= nums.len() <= 100, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        ensures
            0 <= res <= 100,
            res == Self::count_values_in_range(nums@, 1, 101),
    {
        let mut freqs: [bool; 101] = [false;101];

        for i in 0..nums.len()
        {
            freqs[nums[i] as usize] = true;
        }

        let mut ans: u8 = 0;
        for idx in 1..101 
        {
            if freqs[idx] == true {
                ans += 1;
            }
        }
        ans as i32
    }
}

}