use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_dim(vec: Seq<i32>, n: int, d: int) -> int
    recommends
        0 <= d < 3,
        0 <= n,
        3 * n <= vec.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        vec[3 * (n - 1) + d] as int + sum_dim(vec, n - 1, d)
    }
}

pub open spec fn forces_equilibrium(vec: Seq<i32>, n: int) -> bool
    recommends
        1 <= n,
        3 * n <= vec.len(),
{
    forall|d: int| 0 <= d < 3 ==> #[trigger] sum_dim(vec, n, d) == 0
}

impl Solution {
    pub fn is_equilibrium(vec: Vec<i32>, n: usize) -> (res: bool)
        requires
            1 <= n <= 100,
            vec.len() == 3 * n,
            forall|i: int| 0 <= i < vec.len() ==> -100 <= #[trigger] vec[i] <= 100,
        ensures
            res == forces_equilibrium(vec@, n as int),
    {
    }
}

}
