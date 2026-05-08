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
        let n = nums.len();
        let mut result = vec![0i32; n];
        let mut i: usize = 0;
        while i < n {
            let delta: i32 = nums[i];
            if delta == 0 {
                result.set(i, nums[i]);
            } else if delta > 0 {
                let mut pos: usize = i;
                let mut step: i32 = 0;
                while step < delta {
                    if pos + 1 < n {
                        pos = pos + 1;
                    } else {
                        pos = 0;
                    }
                    step = step + 1;
                }
                result.set(i, nums[pos]);
            } else {
                let mut pos: usize = i;
                let mut step: i32 = 0;
                let target: i32 = -delta;
                while step < target {
                    if pos > 0 {
                        pos = pos - 1;
                    } else {
                        pos = n - 1;
                    }
                    step = step + 1;
                }
                result.set(i, nums[pos]);
            }
            i = i + 1;
        }
        result
    }
}

}
