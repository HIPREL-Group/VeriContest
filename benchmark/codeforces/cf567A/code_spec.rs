use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub open spec fn min_distance_to_other(x: Seq<i64>, i: int) -> int
    recommends
        0 <= i < x.len(),
        x.len() >= 2,
{
    if i == 0 {
        abs_diff(x[1] as int, x[0] as int)
    } else if i == x.len() - 1 {
        abs_diff(x[i] as int, x[i - 1] as int)
    } else {
        let left = abs_diff(x[i] as int, x[i - 1] as int);
        let right = abs_diff(x[i + 1] as int, x[i] as int);
        if left <= right { left } else { right }
    }
}

pub open spec fn max_distance_to_other(x: Seq<i64>, i: int) -> int
    recommends
        0 <= i < x.len(),
        x.len() >= 2,
{
    let left = abs_diff(x[i] as int, x[0] as int);
    let right = abs_diff(x[x.len() - 1] as int, x[i] as int);
    if left >= right { left } else { right }
}

impl Solution {
    pub fn compute_min_max_distances(x: Vec<i64>) -> (result: Vec<(i64, i64)>)
        requires
            2 <= x.len() <= 100_000,
            forall |i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
            forall |i: int| 0 <= i < x.len() ==> -1_000_000_000 <= #[trigger] x[i] <= 1_000_000_000,
        ensures
            result.len() == x.len(),
            forall |i: int|
                0 <= i < result.len() ==>
                    result[i].0 as int == min_distance_to_other(x@, i)
                    && result[i].1 as int == max_distance_to_other(x@, i)
                    && forall |j: int|
                        0 <= j < x.len() && j != i ==>
                            abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x@, i)
                    && exists |j: int|
                        0 <= j < x.len() && j != i &&
                        abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x@, i)
                    && forall |j: int|
                        0 <= j < x.len() && j != i ==>
                            abs_diff(x[i] as int, x[j] as int) <= max_distance_to_other(x@, i)
                    && exists |j: int|
                        0 <= j < x.len() && j != i &&
                        abs_diff(x[i] as int, x[j] as int) == max_distance_to_other(x@, i),
    {
        let n = x.len();
        let mut result: Vec<(i64, i64)> = Vec::new();
        let mut i = 0usize;
        while i < n {
            let mini;
            let maxi;
            if i == 0 {
                let d1 = if x[1] >= x[0] { x[1] - x[0] } else { x[0] - x[1] };
                let d2 = if x[n - 1] >= x[0] { x[n - 1] - x[0] } else { x[0] - x[n - 1] };
                mini = d1;
                maxi = d2;
            } else if i == n - 1 {
                let d1 = if x[n - 1] >= x[n - 2] { x[n - 1] - x[n - 2] } else { x[n - 2] - x[n - 1] };
                let d2 = if x[n - 1] >= x[0] { x[n - 1] - x[0] } else { x[0] - x[n - 1] };
                mini = d1;
                maxi = d2;
            } else {
                let left_dist = if x[i] >= x[i - 1] { x[i] - x[i - 1] } else { x[i - 1] - x[i] };
                let right_dist = if x[i + 1] >= x[i] { x[i + 1] - x[i] } else { x[i] - x[i + 1] };
                mini = left_dist.min(right_dist);
                let left_end = if x[i] >= x[0] { x[i] - x[0] } else { x[0] - x[i] };
                let right_end = if x[n - 1] >= x[i] { x[n - 1] - x[i] } else { x[i] - x[n - 1] };
                maxi = left_end.max(right_end);
            }
            result.push((mini, maxi));
            i += 1;
        }
        result
    }
}

}
