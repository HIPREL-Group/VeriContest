use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn MOD() -> int {
        1_000_000_007
    }

    pub open spec fn max_pos_spec(steps: int, arr_len: int) -> int {
        if steps / 2 < arr_len - 1 {
            steps / 2
        } else {
            arr_len - 1
        }
    }

    pub open spec fn ways(step: int, pos: int, max_pos: int) -> int
        decreases step,
    {
        if step < 0 || pos < 0 || pos > max_pos {
            0
        } else if step == 0 {
            if pos == 0 { 1 } else { 0 }
        } else {
            Self::ways(step - 1, pos - 1, max_pos)
                + Self::ways(step - 1, pos, max_pos)
                + Self::ways(step - 1, pos + 1, max_pos)
        }
    }

    pub fn num_ways(steps: i32, arr_len: i32) -> (result: i32)
        requires
            1 <= steps <= 500,
            1 <= arr_len <= 1_000_000,
        ensures
            result as int == Self::ways(
                steps as int,
                0,
                Self::max_pos_spec(steps as int, arr_len as int),
            ) % Self::MOD(),
    {
    }
}

}
