use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prev(i: int, n: int) -> int
{
    if i == 0 { n - 1 } else { i - 1 }
}

pub open spec fn spec_next(i: int, n: int) -> int
{
    if i == n - 1 { 0 } else { i + 1 }
}

pub open spec fn spec_is_alternating(colors: Seq<i32>, i: int) -> bool
{
    let n = colors.len() as int;
    colors[i] != colors[spec_prev(i, n)] && colors[i] != colors[spec_next(i, n)]
}

pub open spec fn spec_count_alternating(colors: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_count_alternating(colors, k - 1) + if spec_is_alternating(colors, k - 1) {
            1 as int
        } else {
            0 as int
        }
    }
}

pub open spec fn spec_number_of_alternating_groups(colors: Seq<i32>) -> int
{
    spec_count_alternating(colors, colors.len() as int)
}

proof fn lemma_count_bounds(colors: Seq<i32>, k: int)
    requires
        0 <= k <= colors.len(),
        colors.len() >= 3,
    ensures
        0 <= spec_count_alternating(colors, k) <= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_count_bounds(colors, k - 1);
    }
}

proof fn lemma_prev_mod(i: int, n: int)
    requires
        0 <= i < n,
        n >= 3,
    ensures
        (i + n - 1) % n == spec_prev(i, n),
{
    if i == 0 {
        assert((n - 1) % n == n - 1) by(nonlinear_arith)
            requires n >= 3;
    } else {
        assert((i + n - 1) % n == i - 1) by(nonlinear_arith)
            requires 0 < i < n, n >= 3;
    }
}

proof fn lemma_next_mod(i: int, n: int)
    requires
        0 <= i < n,
        n >= 3,
    ensures
        (i + 1) % n == spec_next(i, n),
{
    if i == n - 1 {
        assert((n - 1 + 1) % n == 0) by(nonlinear_arith)
            requires n >= 3;
    } else {
        assert((i + 1) % n == i + 1) by(nonlinear_arith)
            requires 0 <= i < n - 1, n >= 3;
    }
}

impl Solution {
    pub fn number_of_alternating_groups(colors: Vec<i32>) -> (result: i32)
        requires
            3 <= colors.len() <= 100,
            forall|i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 1,
        ensures
            result as int == spec_number_of_alternating_groups(colors@),
    {
        let n = colors.len();
        let mut count = 0i32;
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == colors.len(),
                3 <= n <= 100,
                forall|j: int| 0 <= j < colors.len() ==> 0 <= #[trigger] colors@[j] <= 1,
                count as int == spec_count_alternating(colors@, i as int),
                0 <= count <= 100,
            decreases n - i,
        {
            proof {
                lemma_count_bounds(colors@, (i + 1) as int);
                lemma_prev_mod(i as int, n as int);
                lemma_next_mod(i as int, n as int);
            }

            let prev = (i + n - 1) % n;
            let next = (i + 1) % n;
            if colors[i] != colors[prev] && colors[i] != colors[next] {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}

}
