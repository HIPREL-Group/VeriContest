use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn perm_fn(n: int, i: int) -> int {
    if i % 2 == 0 { i / 2 } else { n / 2 + (i - 1) / 2 }
}

pub open spec fn iterate_perm(n: int, start: int, steps: nat) -> int
    decreases steps,
{
    if steps == 0 {
        start
    } else {
        perm_fn(n, iterate_perm(n, start, (steps - 1) as nat))
    }
}

impl Solution {
    pub fn reinitialize_permutation(n: i32) -> (res: i32)
        requires
            2 <= n <= 1000,
            n % 2 == 0,
        ensures
            res >= 1,
            iterate_perm(n as int, 1, res as nat) == 1,
            forall |k: int| 1 <= k < res
                ==> #[trigger] iterate_perm(n as int, 1, k as nat) != 1,
    {
        if n == 2 {
            return 1;
        }
        let mut val: i32 = n / 2;
        let mut ops: i32 = 1;
        while val != 1 {
            if val % 2 == 0 {
                val = val / 2;
            } else {
                val = n / 2 + (val - 1) / 2;
            }
            ops = ops + 1;
        }
        ops
    }
}

}
