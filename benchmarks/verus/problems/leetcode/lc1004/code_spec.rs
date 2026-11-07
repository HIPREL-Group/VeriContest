use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_zeros(s: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= s.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            (if s[l] == 0 { 1int } else { 0int }) + Self::count_zeros(s, l + 1, r)
        }
    }

    pub fn longest_ones(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] == 0 || nums[i] == 1,
            0 <= k <= nums.len(),
        ensures
            0 <= result <= nums.len(),
            result == 0 || exists|l: int, r: int|
                0 <= l && r == l + result as int && r <= nums.len() as int
                    && #[trigger] Self::count_zeros(nums@, l, r) <= k as int,
            forall|l: int, r: int|
                0 <= l && l <= r && r <= nums.len() as int
                    && #[trigger] Self::count_zeros(nums@, l, r) <= k as int ==> r - l
                    <= result as int,
    {
        let n = nums.len();
        let mut left: usize = 0;
        let mut zeros: i32 = 0;
        let mut result: i32 = 0;
        let mut right: usize = 0;

        while right < n {
            if nums[right] == 0 {
                zeros = zeros + 1;
            }
            right = right + 1;

            while zeros > k {
                if nums[left] == 0 {
                    zeros = zeros - 1;
                }
                left = left + 1;
            }

            let window = (right - left) as i32;
            if window > result {
                result = window;
            }
        }

        result
    }
}

} 
