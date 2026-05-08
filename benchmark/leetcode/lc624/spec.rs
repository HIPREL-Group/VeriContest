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
    }
}

}
