use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn level_cubes(i: int) -> int {
    i * (i + 1) / 2
}

pub open spec fn cumulative_cubes(h: int) -> int
    decreases h,
{
    if h <= 0 {
        0int
    } else {
        cumulative_cubes(h - 1) + level_cubes(h)
    }
}

proof fn lemma_cumulative_step(h: int)
    requires
        h >= 0,
    ensures
        cumulative_cubes(h + 1) == cumulative_cubes(h) + (h + 1) * (h + 2) / 2,
    decreases h,
{
}

proof fn lemma_cumulative_lower(h: int)
    requires
        h >= 0,
    ensures
        cumulative_cubes(h) >= h,
    decreases h,
{
    if h > 0 {
        lemma_cumulative_lower(h - 1);
        assert((h * (h + 1) / 2) >= 1) by (nonlinear_arith) requires h >= 1;
    }
}

impl Solution {
    pub fn max_pyramid_height(n: u64) -> (result: u64)
        requires
            1 <= n <= 10000,
        ensures
            cumulative_cubes(result as int) <= n as int,
            cumulative_cubes(result as int + 1) > n as int,
    {
        let mut h: u64 = 0;
        let mut total: u64 = 0;
        proof {
            assert(cumulative_cubes(0) == 0);
        }
        let mut done: bool = false;
        while !done
            invariant
                n <= 10000,
                h <= 10001,
                total as int == cumulative_cubes(h as int),
                total <= n,
                done ==> cumulative_cubes(h as int + 1) > n as int,
            decreases if done { 0int } else { 10002int - h as int },
        {
            if h >= 10001 {
                done = true;
                proof {
                    lemma_cumulative_lower(h as int + 1);
                    assert(cumulative_cubes(h as int + 1) >= h as int + 1);
                    assert(h as int + 1 > n as int);
                }
            } else {
                assert(h <= 10000);
                assert((h + 1) * (h + 2) <= 10001u64 * 10002u64) by (nonlinear_arith) requires h <= 10000u64;
                let level = (h + 1) * (h + 2) / 2;
                if total + level > n {
                    done = true;
                    proof {
                        lemma_cumulative_step(h as int);
                    }
                } else {
                    proof {
                        lemma_cumulative_step(h as int);
                    }
                    total = total + level;
                    h = h + 1;
                }
            }
        }
        h
    }
}

}
