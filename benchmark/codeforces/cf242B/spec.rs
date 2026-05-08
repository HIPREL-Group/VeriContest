use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn segment_contains(left: Seq<i32>, right: Seq<i32>, i: int, j: int) -> bool
    recommends
        left.len() == right.len(),
        0 <= i < left.len(),
        0 <= j < left.len(),
{
    left[i] <= left[j] && right[j] <= right[i]
}

pub open spec fn covers_all_segments(left: Seq<i32>, right: Seq<i32>, i: int) -> bool
    recommends
        left.len() == right.len(),
        0 <= i < left.len(),
{
    forall|j: int| 0 <= j < left.len() ==> #[trigger] segment_contains(left, right, i, j)
}

impl Solution {
    pub fn find_covering_segment(left: Vec<i32>, right: Vec<i32>) -> (ans: i32)
        requires
            left.len() == right.len(),
            1 <= left.len() <= 100_000,
            forall|i: int| 0 <= i < left.len() ==> 1 <= #[trigger] left[i] <= right[i] <= 1_000_000_000,
            forall|i: int, j: int|
                0 <= i < j < left.len() ==> left[i] != left[j] || right[i] != right[j],
        ensures
            0 <= ans <= left.len(),
            ans != 0 ==> covers_all_segments(left@, right@, ans as int - 1),
            ans == 0 ==> forall|i: int| 0 <= i < left.len() ==> !covers_all_segments(left@, right@, i),
    {
    }
}

}
