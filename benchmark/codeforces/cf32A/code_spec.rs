use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn count_lower(a: Seq<i64>, i: int, j: int, d: int) -> int
    decreases j,
{
    if j <= 0 {
        0int
    } else if abs_diff(a[i] as int, a[j - 1] as int) <= d {
        count_lower(a, i, j - 1, d) + 1
    } else {
        count_lower(a, i, j - 1, d)
    }
}

pub open spec fn count_total(a: Seq<i64>, n: int, d: int) -> int
    decreases n,
{
    if n <= 0 {
        0int
    } else {
        count_total(a, n - 1, d) + count_lower(a, n - 1, n - 1, d)
    }
}

impl Solution {
    pub fn count_recon_pairs(n: usize, d: i64, heights: Vec<i64>) -> (result: u64)
        requires
            1 <= n <= 1000,
            heights.len() == n,
            1 <= d <= 1000000000,
            forall|i: int| 0 <= i < heights.len() ==> 0 <= #[trigger] heights[i] as int <= 1000000000,
        ensures
            result as int == 2 * count_total(heights@, n as int, d as int),
    {
        let mut count: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                let a = heights[i];
                let b = heights[j];
                let diff: i64 = if a >= b { a - b } else { b - a };
                if diff <= d {
                    count = count + 2;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}

}
