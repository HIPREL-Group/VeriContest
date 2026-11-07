use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub fn max_distance(colors: Vec<i32>) -> (result: i32)
        requires
            2 <= colors.len() <= 100,
            forall |i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 100,
            exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j],
        ensures
            result >= 0,
            exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j] && #[trigger] (j - i) == result,
            forall |i: int, j: int| 0 <= i < j < colors.len() ==> colors[i] == colors[j] || #[trigger] (j - i) <= result,
    {
    }
}
}
