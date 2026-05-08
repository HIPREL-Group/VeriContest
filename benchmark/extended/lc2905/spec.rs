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
    }
}

}
