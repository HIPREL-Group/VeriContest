use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_time(heights: Seq<i32>, i: int, cur_h: int) -> int
    decreases heights.len() - i,
{
    if i >= heights.len() {
        0
    } else {
        let target = heights[i] as int;
        let climb = if target > cur_h { target - cur_h } else { cur_h - target };
        if i < heights.len() as int - 1 {
            let next_max = heights[i + 1] as int + 1;
            let extra = if target > next_max { target - next_max } else { 0int };
            let new_h = if target > next_max { next_max } else { target };
            climb + 1 + extra + 1 + spec_time(heights, i + 1, new_h)
        } else {
            climb + 1
        }
    }
}

impl Solution {
    pub fn min_time(heights: Vec<i32>) -> (result: i64)
        requires
            1 <= heights.len() <= 100000,
            forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 10000,
        ensures
            result as int == spec_time(heights@, 0, 0),
    {
        let n = heights.len();
        let mut time = 0i64;
        let mut current_height = 0i32;
        let mut i: usize = 0;
        while i < n {
            let target_height = heights[i];
            let climb: i64 = if target_height > current_height {
                (target_height - current_height) as i64
            } else {
                (current_height - target_height) as i64
            };
            time = time + climb;
            current_height = target_height;
            time = time + 1;
            if i < n - 1 {
                let next_tree_height = heights[i + 1];
                let max_jump_height = next_tree_height + 1;
                if current_height > max_jump_height {
                    let climb_down = (current_height - max_jump_height) as i64;
                    time = time + climb_down;
                    current_height = max_jump_height;
                }
                time = time + 1;
            }
            i = i + 1;
        }
        time
    }
}

}
