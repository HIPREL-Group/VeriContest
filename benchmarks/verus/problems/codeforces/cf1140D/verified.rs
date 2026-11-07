use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn triangulation_sum(n: int) -> int
    decreases n,
{
    if n <= 2 {
        0int
    } else {
        triangulation_sum(n - 1) + (n - 1) * n
    }
}

proof fn lemma_sum_bound(n: int)
    requires
        2 <= n <= 500,
    ensures
        0 <= triangulation_sum(n) <= 250_000 * n,
    decreases n,
{
    if n <= 2 {
    } else {
        lemma_sum_bound(n - 1);
        
        
        
        
        assert((n - 1) * n <= 500 * 500) by(nonlinear_arith)
            requires n <= 500, n >= 0;
    }
}

impl Solution {
    pub fn min_triangulation(n: u32) -> (res: u64)
        requires
            3 <= n <= 500,
        ensures
            res as int == triangulation_sum(n as int),
    {
        let mut sum: u64 = 0;
        let mut i: u32 = 2;
        while i < n
            invariant
                2 <= i <= n,
                3 <= n <= 500,
                sum as int == triangulation_sum(i as int),
                sum <= 250_000u64 * (i as u64),
            decreases n - i,
        {
            proof {
                lemma_sum_bound(i as int);
            }
            assert(i < 500);
            let i64v: u64 = i as u64;
            assert(i64v < 500);
            assert(i64v * (i64v + 1) <= 500u64 * 501u64) by(nonlinear_arith)
                requires i64v < 500;
            let term: u64 = i64v * (i64v + 1);
            sum = sum + term;
            i = i + 1;
            proof {
                lemma_sum_bound(i as int);
            }
        }
        sum
    }
}

}
