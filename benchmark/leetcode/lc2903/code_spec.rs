use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_int(x: int) -> int {
        if x < 0 { -x } else { x }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, i: int, j: int, index_difference: int, value_difference: int) -> bool
        recommends
            0 <= i < nums.len(),
            0 <= j < nums.len(),
            0 <= index_difference,
            0 <= value_difference,
    {
        Self::abs_int(i - j) >= index_difference
            && Self::abs_int(nums[i] as int - nums[j] as int) >= value_difference
    }

    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            0 <= index_difference <= 100,
            0 <= value_difference <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50,
        ensures
            result.len() == 2,
            result[0] == -1 ==> result[1] == -1,
            result[0] != -1 ==> (
                0 <= result[0] < nums.len() as i32
                && 0 <= result[1] < nums.len() as i32
                && Self::valid_pair(nums@, result[0] as int, result[1] as int, index_difference as int, value_difference as int)
            ),
            result[0] == -1 ==> (
                forall |i: i32, j: i32|
                    0 <= i < nums.len() as i32 && 0 <= j < nums.len() as i32
                    ==> !Self::valid_pair(nums@, i as int, j as int, index_difference as int, value_difference as int)
            ),
    {
        let mut i: i32 = 0;
        while i < nums.len() as i32 {
            let mut j: i32 = 0;
            while j < nums.len() as i32 {
                let idx_gap: i32 = if i >= j { i - j } else { j - i };
                let val_gap: i64 = if nums[i as usize] >= nums[j as usize] {
                    nums[i as usize] as i64 - nums[j as usize] as i64
                } else {
                    nums[j as usize] as i64 - nums[i as usize] as i64
                };
                if idx_gap >= index_difference && val_gap >= value_difference as i64 {
                    return vec![i, j];
                }
                j = j + 1;
            }
            i = i + 1;
        }
        vec![-1, -1]
    }
}

}
