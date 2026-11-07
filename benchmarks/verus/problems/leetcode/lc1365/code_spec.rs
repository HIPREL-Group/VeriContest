use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_less_than(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() < val { 1int } else { 0int }) + Self::count_less_than(s.drop_last(), val)
        }
    }

    pub fn smaller_numbers_than_current(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] as int == Self::count_less_than(nums@, nums[i]),
    {
        let n = nums.len();
        let mut freq: Vec<i32> = Vec::new();
        let mut v: usize = 0;
        while v <= 100 {
            freq.push(0);
            v = v + 1;
        }
        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            freq.set(val, freq[val] + 1);
            i = i + 1;
        }
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut v: usize = 1;
        while v <= 100 {
            prefix.push(prefix[v - 1] + freq[v - 1]);
            v = v + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            result.push(prefix[nums[i] as usize]);
            i = i + 1;
        }
        result
    }
}

}
