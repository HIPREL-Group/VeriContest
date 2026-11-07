use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_good_pair(nums: Seq<i32>, i: int, j: int) -> bool {
    0 <= i < j < nums.len()
    && nums[i] == nums[j]
}

pub open spec fn count_inner(nums: Seq<i32>, i: int, j: int) -> int
    decreases j - i - 1,
{
    if j <= i + 1 {
        0
    } else {
        count_inner(nums, i, j - 1)
            + if is_good_pair(nums, i, j - 1) { 1int } else { 0int }
    }
}

pub open spec fn count_all(nums: Seq<i32>, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() {
        0
    } else {
        count_all(nums, i + 1) + count_inner(nums, i, nums.len() as int)
    }
}

impl Solution {
    pub fn num_identical_pairs(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            res as int == count_all(nums@, 0),
    {
        let n = nums.len();
        let mut count: i64 = 0;
        let mut i: usize = 0;

        while i < n
        {
            let mut j: usize = i + 1;

            while j < n
            {
                if nums[i] == nums[j] {
                    count = count + 1;
                }
                j += 1;
            }
            i += 1;
        }

        count as i32
    }
}

} 
