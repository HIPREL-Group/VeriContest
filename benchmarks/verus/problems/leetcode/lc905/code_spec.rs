use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub open spec fn count_in_range(s: Seq<i32>, v: i32, start: int, end: int) -> int
        decreases end - start when start <= end
    {
        if start >= end {
            0
        } else {
            (if s[start] == v { 1int } else { 0int }) + Self::count_in_range(s, v, start + 1, end)
        }
    }

    pub fn sort_array_by_parity(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 5000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 5000,
        ensures
            result.len() == nums.len(),
            forall |i: int, j: int| 0 <= i < j < result.len() && result[j] % 2 == 0
                ==> result[i] % 2 == 0,
            forall |v: i32| Self::count(result@, v) == Self::count(nums@, v),
    {
        let mut result = nums;
        let n = result.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;

        while left < right {
            if result[left] % 2 != 0 && result[right] % 2 == 0 {
                let tmp_left = result[left];
                let tmp_right = result[right];
                result.set(left, tmp_right);
                result.set(right, tmp_left);
                left = left + 1;
                right = right - 1;
            } else if result[left] % 2 == 0 {
                left = left + 1;
            } else {
                right = right - 1;
            }
        }
        result
    }
}

}
