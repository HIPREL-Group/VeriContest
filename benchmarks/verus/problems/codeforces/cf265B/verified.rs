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

proof fn lemma_spec_time_nonneg(heights: Seq<i32>, i: int, cur_h: int)
    requires
        i >= 0,
        cur_h >= 0,
        forall|j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights[j] <= 10000,
    ensures
        spec_time(heights, i, cur_h) >= 0,
    decreases heights.len() - i,
{
    if i < heights.len() as int {
        if i < heights.len() as int - 1 {
            let target = heights[i] as int;
            let next_max = heights[i + 1] as int + 1;
            let new_h: int = if target > next_max { next_max } else { target };
            lemma_spec_time_nonneg(heights, i + 1, new_h);
        }
    }
}

proof fn lemma_spec_time_upper(heights: Seq<i32>, i: int, cur_h: int)
    requires
        0 <= i <= heights.len(),
        0 <= cur_h <= 10001,
        heights.len() <= 100000,
        forall|j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights[j] <= 10000,
    ensures
        spec_time(heights, i, cur_h) <= 20003 * (heights.len() as int - i),
    decreases heights.len() as int - i,
{
    if i < heights.len() as int {
        if i < heights.len() as int - 1 {
            let target = heights[i] as int;
            let next_max = heights[i + 1] as int + 1;
            let new_h: int = if target > next_max { next_max } else { target };
            assert(0 <= new_h <= 10001);
            lemma_spec_time_upper(heights, i + 1, new_h);
            assert(20003 + 20003 * (heights.len() as int - i - 1)
                == 20003 * (heights.len() as int - i)) by (nonlinear_arith)
                requires i + 1 <= heights.len() as int;
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

        proof {
            lemma_spec_time_upper(heights@, 0, 0);
            assert(spec_time(heights@, 0, 0) <= 2_000_300_000) by (nonlinear_arith)
                requires
                    spec_time(heights@, 0, 0) <= 20003 * (heights@.len() as int),
                    heights@.len() <= 100000;
            lemma_spec_time_nonneg(heights@, 0, 0);
        }

        let ghost total = spec_time(heights@, 0, 0);

        while i < n
            invariant
                0 <= i <= n,
                n == heights.len(),
                1 <= n <= 100000,
                0 <= current_height <= 10001,
                0 <= time,
                time as int == total - spec_time(heights@, i as int, current_height as int),
                total == spec_time(heights@, 0, 0),
                0 <= total <= 2_000_300_000,
                forall|j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights[j] <= 10000,
            decreases n - i,
        {
            proof {
                lemma_spec_time_nonneg(heights@, i as int, current_height as int);
            }

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

            proof {
                assert(time as int == total
                    - spec_time(heights@, (i + 1) as int, current_height as int));
            }

            i = i + 1;
        }

        time
    }
}

}
