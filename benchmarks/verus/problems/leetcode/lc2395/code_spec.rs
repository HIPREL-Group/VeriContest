use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_subarrays(nums: Vec<i32>) -> (result: bool)
        requires
            2 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result == (exists|i: int, j: int|
                0 <= i < j && j + 1 < nums.len() as int
                && (#[trigger] nums[i]) as int + nums[i + 1] as int == (#[trigger] nums[j]) as int + nums[j + 1] as int),
    {
        let n = nums.len();
        if n < 2 {
            return false;
        }
        let mut i: usize = 0;
        while i < n - 1 {
            let s1: i64 = nums[i] as i64 + nums[i + 1] as i64;
            let mut j: usize = i + 1;
            while j < n - 1 {
                let s2: i64 = nums[j] as i64 + nums[j + 1] as i64;
                if s1 == s2 {
                    return true;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        false
    }
}

}
