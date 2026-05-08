use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(x: int, y: int) -> int {
        if x >= y {
            x - y
        } else {
            y - x
        }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, index_difference: int, value_difference: int, i: int, j: int) -> bool {
        &&& 0 <= i < nums.len()
        &&& 0 <= j < nums.len()
        &&& Self::abs_diff(i, j) >= index_difference
        &&& Self::abs_diff(nums[i] as int, nums[j] as int) >= value_difference
    }

    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            0 <= index_difference <= 100_000,
            0 <= value_difference <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result.len() == 2,
            (result[0] == -1i32) == (result[1] == -1i32),
            result[0] == -1i32 ==> forall |i: int, j: int|
                0 <= i < nums.len() && 0 <= j < nums.len()
                    ==> !Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j),
            (exists |i: int, j: int| Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j))
                ==> result[0] != -1i32,
            result[0] != -1i32 ==> Self::valid_pair(
                nums@,
                index_difference as int,
                value_difference as int,
                result[0] as int,
                result[1] as int,
            ),
    {
        let n = nums.len();
        let index_difference_usize = index_difference as usize;

        if index_difference_usize >= n {
            let mut result = Vec::new();
            result.push(-1i32);
            result.push(-1i32);
            return result;
        }

        let mut r: usize = index_difference_usize;
        let mut min_idx: usize = 0;
        let mut max_idx: usize = 0;

        while r < n
        {
            let high_gap = nums[max_idx] - nums[r];
            if high_gap >= value_difference {
                let mut result = Vec::new();
                result.push(max_idx as i32);
                result.push(r as i32);
                return result;
            }

            let low_gap = nums[r] - nums[min_idx];
            if low_gap >= value_difference {
                let mut result = Vec::new();
                result.push(min_idx as i32);
                result.push(r as i32);
                return result;
            }

            r = r + 1;
            if r < n {
                let add_idx = r - index_difference_usize;

                if nums[add_idx] < nums[min_idx] {
                    min_idx = add_idx;
                } else {
                }

                if nums[add_idx] > nums[max_idx] {
                    max_idx = add_idx;
                } 
            }
        }

        let mut result = Vec::new();
        result.push(-1i32);
        result.push(-1i32);
        result
    }
}

}
