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

proof fn lemma_count_lower_bound(a: Seq<i64>, i: int, j: int, d: int)
    requires
        0 <= j,
    ensures
        0 <= count_lower(a, i, j, d) <= j,
    decreases j,
{
    if j > 0 {
        lemma_count_lower_bound(a, i, j - 1, d);
    }
}

proof fn lemma_count_total_bound(a: Seq<i64>, n: int, d: int)
    requires
        0 <= n,
    ensures
        0 <= count_total(a, n, d) <= n * n,
    decreases n,
{
    if n > 0 {
        lemma_count_total_bound(a, n - 1, d);
        lemma_count_lower_bound(a, n - 1, n - 1, d);
        assert((n - 1) * (n - 1) + (n - 1) <= n * n) by (nonlinear_arith) requires n >= 1;
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
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 1000,
                heights.len() == n,
                1 <= d <= 1000000000,
                forall|k: int| 0 <= k < heights.len() ==> 0 <= #[trigger] heights[k] as int <= 1000000000,
                count as int == 2 * count_total(heights@, i as int, d as int),
            decreases n - i,
        {
            proof {
                lemma_count_total_bound(heights@, i as int, d as int);
                assert(i as int * i as int <= 1000 * 1000) by (nonlinear_arith) requires i <= 1000usize;
                assert(count as int <= 4 * 1000 * 1000);
            }
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    0 <= i < n,
                    1 <= n <= 1000,
                    heights.len() == n,
                    1 <= d <= 1000000000,
                    forall|k: int| 0 <= k < heights.len() ==> 0 <= #[trigger] heights[k] as int <= 1000000000,
                    count as int == 2 * count_total(heights@, i as int, d as int) + 2 * count_lower(heights@, i as int, j as int, d as int),
                    count as int <= 4 * 1000 * 1000,
                decreases i - j,
            {
                let a = heights[i];
                let b = heights[j];
                let diff: i64 = if a >= b { a - b } else { b - a };
                proof {
                    assert(diff as int == abs_diff(a as int, b as int));
                    assert(a as int == heights@[i as int] as int);
                    assert(b as int == heights@[j as int] as int);
                    lemma_count_total_bound(heights@, i as int, d as int);
                    lemma_count_lower_bound(heights@, i as int, j as int, d as int);
                    lemma_count_lower_bound(heights@, i as int, (j + 1) as int, d as int);
                    assert(i as int * i as int <= 1000 * 1000) by (nonlinear_arith) requires i <= 1000usize;
                }
                if diff <= d {
                    count = count + 2;
                }
                j = j + 1;
            }
            proof {
                assert(j == i);
                assert(count_total(heights@, (i + 1) as int, d as int) ==
                    count_total(heights@, i as int, d as int) + count_lower(heights@, i as int, i as int, d as int));
            }
            i = i + 1;
        }
        count
    }
}

}
