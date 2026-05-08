use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_seq(a: Seq<u64>) -> u64
    recommends
        a.len() > 0,
    decreases a.len(),
{
    if a.len() <= 1 {
        a[0]
    } else {
        let m = min_seq(a.subrange(0, a.len() - 1));
        if a[a.len() - 1] < m {
            a[a.len() - 1]
        } else {
            m
        }
    }
}

pub open spec fn max_int(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

pub open spec fn cost_sum(a: Seq<u64>, b: Seq<u64>, ma: u64, mb: u64) -> int
    recommends
        a.len() == b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        let last = a.len() - 1;
        let prev = cost_sum(a.subrange(0, last), b.subrange(0, last), ma, mb);
        prev + max_int(a[last] as int - ma as int, b[last] as int - mb as int)
    }
}

impl Solution {
    pub fn min_moves_to_equalize(n: usize, a: Vec<u64>, b: Vec<u64>) -> (result: u64)
        requires
            1 <= n <= 50,
            a.len() == n,
            b.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000u64,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1_000_000_000u64,
        ensures
            result as int == cost_sum(a@, b@, min_seq(a@), min_seq(b@)),
    {
    }
}

}
