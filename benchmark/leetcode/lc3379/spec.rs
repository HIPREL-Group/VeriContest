use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn step_right(pos: int, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
    {
        if pos + 1 < n { pos + 1 } else { 0 }
    }

    pub open spec fn step_left(pos: int, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
    {
        if pos > 0 { pos - 1 } else { n - 1 }
    }

    pub open spec fn move_right(pos: int, steps: nat, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
        decreases steps,
    {
        if steps == 0 {
            pos
        } else {
            Self::step_right(Self::move_right(pos, (steps - 1) as nat, n), n)
        }
    }

    pub open spec fn move_left(pos: int, steps: nat, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
        decreases steps,
    {
        if steps == 0 {
            pos
        } else {
            Self::step_left(Self::move_left(pos, (steps - 1) as nat, n), n)
        }
    }

    pub open spec fn transformed_index(nums: Seq<i32>, i: int) -> int
        recommends
            nums.len() > 0,
            0 <= i < nums.len(),
    {
        let delta = nums[i] as int;
        if delta >= 0 {
            Self::move_right(i, delta as nat, nums.len() as int)
        } else {
            Self::move_left(i, (-delta) as nat, nums.len() as int)
        }
    }

    pub fn construct_transformed_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] == nums[Self::transformed_index(nums@, i)],
    {
    }
}

}
