use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const MOD: i64 = 1_000_000_007;

    pub open spec fn last_occurrence(nums: Seq<i32>, target: i32, upto: int) -> int
        decreases upto
    {
        if upto <= 0 {
            -1
        } else if nums[upto - 1] == target {
            upto - 1
        } else {
            Self::last_occurrence(nums, target, upto - 1)
        }
    }

    pub open spec fn close_block(nums: Seq<i32>, processed: int, frontier: int) -> int
        recommends
            0 <= processed <= nums.len(),
            -1 <= frontier < nums.len(),
        decreases nums.len() - processed
    {
        if processed >= nums.len() || processed > frontier {
            frontier
        } else {
            let last = Self::last_occurrence(nums, nums[processed], nums.len() as int);
            let new_frontier = if last > frontier { last } else { frontier };
            Self::close_block(nums, processed + 1, new_frontier)
        }
    }

    pub open spec fn block_end(nums: Seq<i32>, start: int) -> int
        recommends
            0 <= start < nums.len(),
    {
        let first = Self::last_occurrence(nums, nums[start], nums.len() as int);
        Self::close_block(nums, start + 1, first)
    }

    pub open spec fn number_of_good_partitions_from(nums: Seq<i32>, start: int) -> int
        recommends
            0 <= start <= nums.len(),
        decreases nums.len() - start
    {
        if start >= nums.len() {
            1
        } else {
            let next = Self::block_end(nums, start) + 1;
            if next <= start || next >= nums.len() {
                1
            } else {
                (2 * Self::number_of_good_partitions_from(nums, next)) % (Self::MOD as int)
            }
        }
    }

    pub open spec fn number_of_good_partitions_spec(nums: Seq<i32>) -> int {
        Self::number_of_good_partitions_from(nums, 0)
    }

    pub fn number_of_good_partitions(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= result < Self::MOD,
            result as int == Self::number_of_good_partitions_spec(nums@),
    {
    }
}

}
