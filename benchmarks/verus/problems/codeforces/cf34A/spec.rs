use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn next_circle(i: int, n: int) -> int
    recommends 0 <= i < n, n >= 1,
{
    if i + 1 < n {
        i + 1
    } else {
        0
    }
}

pub open spec fn adjacent_circle(i: int, j: int, n: int) -> bool
    recommends 0 <= i < n, 0 <= j < n, n >= 2,
{
    j == next_circle(i, n) || i == next_circle(j, n)
}

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub open spec fn adj_diff_at(heights: Seq<i32>, i: int, n: int) -> int
    recommends 0 <= i < n, 2 <= n <= heights.len(),
{
    abs_diff(heights[i] as int, heights[next_circle(i, n)] as int)
}

impl Solution {
    pub fn min_adjacent_pair(heights: Vec<i32>, n: usize) -> (result: (usize, usize))
        requires
            2 <= n <= 100,
            heights.len() == n,
            forall|i: int| 0 <= i < heights.len() as int ==> 1 <= #[trigger] heights[i] as int <= 1000,
        ensures
            0 <= result.0 < n as int,
            0 <= result.1 < n as int,
            adjacent_circle(result.0 as int, result.1 as int, n as int),
            forall|i: int, j: int|
                0 <= i < n as int && 0 <= j < n as int && adjacent_circle(i, j, n as int) ==>
                abs_diff(heights@[i] as int, heights@[j] as int)
                    >= abs_diff(heights@[result.0 as int] as int, heights@[result.1 as int] as int),
            exists|i: int, j: int|
                0 <= i < n as int && 0 <= j < n as int
                && adjacent_circle(i, j, n as int)
                && i == result.0 as int
                && j == result.1 as int
                && abs_diff(heights@[i] as int, heights@[j] as int)
                    == abs_diff(heights@[result.0 as int] as int, heights@[result.1 as int] as int),
    {
    }
}

}
