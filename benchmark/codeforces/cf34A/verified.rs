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
        let mut best_i = 0usize;
        let mut best_j = 1usize;
        let d0 = heights[0] - heights[1];
        let mut min_d = if d0 >= 0 { d0 } else { -d0 };
        let mut i = 1usize;
        while i < n
            invariant
                2 <= n <= 100,
                heights.len() == n,
                forall|k: int| 0 <= k < heights.len() as int ==> 1 <= #[trigger] heights[k] as int <= 1000,
                1 <= i <= n,
                0 <= best_i < n as int,
                0 <= best_j < n as int,
                adjacent_circle(best_i as int, best_j as int, n as int),
                min_d as int == abs_diff(heights@[best_i as int] as int, heights@[best_j as int] as int),
                forall|k: int| 0 <= k < i as int ==> adj_diff_at(heights@, k, n as int) >= min_d as int,
            decreases n - i,
        {
            let j = if i + 1 < n { i + 1 } else { 0 };
            let d = heights[i] - heights[j];
            let d_abs = if d >= 0 { d } else { -d };
            if d_abs < min_d {
                min_d = d_abs;
                best_i = i;
                best_j = j;
            }
            i += 1;
        }
        proof {
            assert(forall|k: int| 0 <= k < n as int ==> adj_diff_at(heights@, k, n as int) >= min_d as int);
            assert forall|ii: int, jj: int|
                (0 <= ii < n as int && 0 <= jj < n as int && adjacent_circle(ii, jj, n as int)) implies
                abs_diff(heights@[ii] as int, heights@[jj] as int)
                    >= abs_diff(heights@[best_i as int] as int, heights@[best_j as int] as int)
            by {
                if 0 <= ii < n as int && 0 <= jj < n as int && adjacent_circle(ii, jj, n as int) {
                    reveal(adjacent_circle);
                    reveal(next_circle);
                    if jj == next_circle(ii, n as int) {
                        assert(adj_diff_at(heights@, ii, n as int)
                            == abs_diff(heights@[ii] as int, heights@[jj] as int));
                        assert(adj_diff_at(heights@, ii, n as int) >= min_d as int);
                    } else {
                        assert(ii == next_circle(jj, n as int));
                        assert(adj_diff_at(heights@, jj, n as int)
                            == abs_diff(heights@[jj] as int, heights@[ii] as int));
                        assert(abs_diff(heights@[jj] as int, heights@[ii] as int)
                            == abs_diff(heights@[ii] as int, heights@[jj] as int));
                        assert(adj_diff_at(heights@, jj, n as int) >= min_d as int);
                    }
                }
            };
        }
        (best_i, best_j)
    }
}

}
