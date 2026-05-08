use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_contrib(a: int, b: int, c: int, d: int) -> int {
    let a_after = if a > c {
        c
    } else {
        a
    };
    let part1 = if a > c {
        a - c
    } else {
        0
    };
    let part2 = if b > d {
        b - d + a_after
    } else {
        0
    };
    part1 + part2
}

pub open spec fn spec_ops_prefix(
    a: Seq<i64>,
    b: Seq<i64>,
    c: Seq<i64>,
    d: Seq<i64>,
    hi: int,
) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        spec_ops_prefix(a, b, c, d, hi - 1) + spec_contrib(
            a[hi] as int,
            b[hi] as int,
            c[hi] as int,
            d[hi] as int,
        )
    }
}

impl Solution {
    pub fn min_pile_shuffle_operations(a: &Vec<i64>, b: &Vec<i64>, c: &Vec<i64>, d: &Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 200_000,
            a.len() == b.len(),
            a.len() == c.len(),
            a.len() == d.len(),
            forall|j: int|
                #![trigger a[j]]
                0 <= j && j < a.len() ==> 0 <= #[trigger] a[j] && a[j] <= 1_000_000_000,
            forall|j: int|
                #![trigger b[j]]
                0 <= j && j < b.len() ==> 0 <= #[trigger] b[j] && b[j] <= 1_000_000_000,
            forall|j: int|
                #![trigger c[j]]
                0 <= j && j < c.len() ==> 0 <= #[trigger] c[j] && c[j] <= 1_000_000_000,
            forall|j: int|
                #![trigger d[j]]
                0 <= j && j < d.len() ==> 0 <= #[trigger] d[j] && d[j] <= 1_000_000_000,
        ensures
            result as int == spec_ops_prefix(a@, b@, c@, d@, (a.len() as int) - 1),
    {
    }
}

}
