use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn total_len(arrays: Seq<Vec<i32>>) -> int
        decreases arrays.len(),
    {
        if arrays.len() == 0 {
            0
        } else {
            arrays[0].len() + Self::total_len(arrays.drop_first())
        }
    }

    pub open spec fn abs_diff(x: int, y: int) -> int {
        if x >= y { x - y } else { y - x }
    }

    pub fn max_distance(arrays: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= arrays.len() <= 100_000,
            forall |a: int| 0 <= a < arrays.len() ==> 1 <= #[trigger] arrays[a].len() <= 500,
            Self::total_len(arrays@) <= 100_000,
            forall |a: int, i: int| 0 <= a < arrays.len() && 0 <= i < arrays[a].len() ==>
                -10_000 <= #[trigger] arrays[a][i] <= 10_000,
            forall |a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() ==>
                arrays[a][i] <= arrays[a][j],
        ensures
            result >= 0,
            exists |a: int, b: int, i: int, j: int|
                0 <= a < arrays.len()
                && 0 <= b < arrays.len()
                && a != b
                && 0 <= i < arrays[a].len()
                && 0 <= j < arrays[b].len()
                && #[trigger] Self::abs_diff(arrays[a][i] as int, arrays[b][j] as int) == result as int,
            forall |a: int, b: int, i: int, j: int|
                0 <= a < arrays.len()
                && 0 <= b < arrays.len()
                && a != b
                && 0 <= i < arrays[a].len()
                && 0 <= j < arrays[b].len()
                ==> #[trigger] Self::abs_diff(arrays[a][i] as int, arrays[b][j] as int) <= result as int,
    {
        let mut min_val = arrays[0][0];
        let mut max_val = arrays[0][arrays[0].len() - 1];
        let mut result = 0i32;
        let mut i: usize = 1;
        while i < arrays.len()
        {
            let curr_len = arrays[i].len();
            let curr_last = curr_len - 1;
            let curr_min = arrays[i][0];
            let curr_max = arrays[i][curr_last];
            let old_min_val = min_val;
            let old_max_val = max_val;
            let old_result = result;

            let mut candidate = curr_max - old_min_val;
            let other = old_max_val - curr_min;
            if other > candidate {
                candidate = other;
            }
            if i == 1 || candidate > result {
                result = candidate;
            }

            if curr_min < min_val {
                min_val = curr_min;
            }
            if curr_max > max_val {
                max_val = curr_max;
            }

            i += 1;
        }
        result
    }
}

}
