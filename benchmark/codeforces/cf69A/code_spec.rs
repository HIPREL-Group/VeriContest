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
        let mut sum_x = 0i64;
        let mut sum_y = 0i64;
        let mut sum_z = 0i64;
        let mut i = 0usize;
        while i < n {
            sum_x += vec[3 * i] as i64;
            sum_y += vec[3 * i + 1] as i64;
            sum_z += vec[3 * i + 2] as i64;
            i += 1;
        }
        sum_x == 0 && sum_y == 0 && sum_z == 0
    }
}

}
