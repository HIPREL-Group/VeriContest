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
        let mut ma: u64 = a[0];
        let mut mb: u64 = b[0];
        let mut i: usize = 1;
        while i < n {
            if a[i] < ma { ma = a[i]; }
            if b[i] < mb { mb = b[i]; }
            i += 1;
        }
        let mut total: u64 = 0;
        let mut j: usize = 0;
        while j < n {
            let da = a[j] - ma;
            let db = b[j] - mb;
            let m = if da >= db { da } else { db };
            total = total + m;
            j += 1;
        }
        total
    }
}

}
