use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub fn search(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            -10_000 < target < 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 < #[trigger] nums[i] < 10_000,
            forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
        ensures
            -1 <= res < nums.len(),
            res == -1 ==> (forall |i: int| 0 <= i < nums.len() ==> nums[i] != target),
            res != -1 ==> nums[res as int] == target,
    {
        let mut i1: usize = 0;
        let mut i2: usize = nums.len() - 1;

        while i1 != i2
            invariant
                1 <= nums.len() <= 10_000,
                forall |i: int| 0 <= i < nums.len() ==> -10_000 < #[trigger] nums[i] < 10_000,
                forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
                i1 <= i2 < nums.len(),
                forall |t: int| 0 <= t < i1 ==> nums[t] < target,
                nums[i2 as int] >= target || i2 == nums.len() - 1,
            decreases i2 - i1,
        {
            let ix = i1 + (i2 - i1) / 2;
            if nums[ix] < target {
                proof {
                    assert forall |t: int| 0 <= t < (ix + 1) as int implies nums[t] < target by {
                        if t < i1 as int {
                        } else if t < ix as int {
                            assert(nums[t] < nums[ix as int]);
                        }
                    }
                }
                i1 = ix + 1;
            } else {
                i2 = ix;
            }
        }

        if nums[i1] != target {
            proof {
                assert forall |t: int| 0 <= t < nums.len() implies nums[t] != target by {
                    if t < i1 as int {
                    } else if t == i1 as int {
                    } else {
                        assert(nums[i1 as int] >= target);
                        assert(nums[i1 as int] < nums[t]);
                    }
                }
            }
            -1
        }
        else {
            i1 as i32
        }
    }

}

}
