use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

pub open spec fn asc_sum_ending_at(nums: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        nums[0] as int
    } else if nums[i] > nums[i - 1] {
        asc_sum_ending_at(nums, i - 1) + nums[i] as int
    } else {
        nums[i] as int
    }
}

pub open spec fn max_val(nums: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo + 1
{
    if lo > hi {
        0
    } else if lo == hi {
        asc_sum_ending_at(nums, hi)
    } else {
        let a = asc_sum_ending_at(nums, hi);
        let b = max_val(nums, lo, hi - 1);
        if a >= b { a } else { b }
    }
}

impl Solution {
    pub fn max_ascending_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (max_val(nums@, 0, (nums.len() - 1) as int) as i32),
    {
        let mut result = nums[0];
        let mut cur = nums[0];
        let mut i = 1usize;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100,
                1 <= i <= nums.len(),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                cur as int == asc_sum_ending_at(nums@, (i - 1) as int),
                result as int == max_val(nums@, 0, (i - 1) as int),
                1 <= cur as int <= 100 * i,
                1 <= result as int <= 100 * i
            decreases nums.len() - i
        {
            proof {
                let idx = i as int;
                let prev = (i - 1) as int;
                assert(1 <= nums[idx]) by {
                    assert(1 <= nums[idx] <= 100);
                }
                if nums[idx] > nums[prev] {
                    assert(asc_sum_ending_at(nums@, idx) == asc_sum_ending_at(nums@, prev) + nums[idx] as int);
                } else {
                    assert(asc_sum_ending_at(nums@, idx) == nums[idx] as int);
                }
                assert(max_val(nums@, 0, idx) == if asc_sum_ending_at(nums@, idx) >= max_val(nums@, 0, prev) { asc_sum_ending_at(nums@, idx) } else { max_val(nums@, 0, prev) });
            }
            if nums[i] > nums[i - 1] {
                cur += nums[i];
            } else {
                cur = nums[i];
            }
            if cur > result {
                result = cur;
            }
            i += 1;
        }
        result
    }
}
}
