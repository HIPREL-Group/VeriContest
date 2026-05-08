use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

pub open spec fn count_neg(nums: Seq<i32>) -> int
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else if nums.last() < 0 {
        count_neg(nums.drop_last()) + 1
    } else {
        count_neg(nums.drop_last())
    }
}

pub open spec fn count_pos(nums: Seq<i32>) -> int
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else if nums.last() > 0 {
        count_pos(nums.drop_last()) + 1
    } else {
        count_pos(nums.drop_last())
    }
}

impl Solution {
    pub fn maximum_count(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> -2000 <= #[trigger] nums[i] <= 2000,
        ensures
            result == if count_pos(nums@) >= count_neg(nums@) { count_pos(nums@) as i32 } else { count_neg(nums@) as i32 },
    {
        let mut neg: i32 = 0;
        let mut pos: i32 = 0;
        let mut i = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 2000,
                neg == count_neg(nums@.take(i as int)),
                pos == count_pos(nums@.take(i as int)),
                0 <= neg <= i,
                0 <= pos <= i
            decreases nums.len() - i
        {
            proof {
                let old_take = nums@.take(i as int);
                let new_take = nums@.take((i + 1) as int);
                assert(new_take.drop_last() =~= old_take);
                assert(new_take.last() == nums[i as int]);
            }
            if nums[i] < 0 {
                neg += 1;
            } else if nums[i] > 0 {
                pos += 1;
            }
            i += 1;
        }
        proof {
            assert(nums@.take(nums.len() as int) =~= nums@);
        }
        if pos >= neg { pos } else { neg }
    }
}
}
