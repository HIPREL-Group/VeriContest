use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

pub open spec fn is_covered_spec(ranges: Seq<Vec<i32>>, x: int) -> bool {
    exists |j: int| 0 <= j < ranges.len() && #[trigger] ranges[j][0] <= x && x <= ranges[j][1]
}

impl Solution {
    pub fn is_covered(ranges: Vec<Vec<i32>>, left: i32, right: i32) -> (result: bool)
        requires
            1 <= ranges.len() <= 50,
            1 <= left <= right <= 50,
            forall |j: int| 0 <= j < ranges.len() ==> #[trigger] ranges[j]@.len() == 2,
            forall |j: int| 0 <= j < ranges.len() ==> 1 <= #[trigger] ranges[j][0] && ranges[j][0] <= ranges[j][1] && ranges[j][1] <= 50,
        ensures
            result <==> forall |i: int| left <= i <= right ==> #[trigger] is_covered_spec(ranges@, i),
    {
    }
}
}
