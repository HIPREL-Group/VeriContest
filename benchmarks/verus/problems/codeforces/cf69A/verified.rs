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

proof fn lemma_sum_dim_step(vec: Seq<i32>, n: int, d: int)
    requires
        0 <= d < 3,
        0 <= n,
        3 * (n + 1) <= vec.len(),
    ensures
        sum_dim(vec, n + 1, d) == sum_dim(vec, n, d) + vec[3 * n + d] as int,
    decreases n,
{
    reveal_with_fuel(sum_dim, 3);
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
        while i < n
            invariant
                1 <= n <= 100,
                vec.len() == 3 * n,
                forall|j: int| 0 <= j < vec.len() ==> -100 <= #[trigger] vec[j] <= 100,
                0 <= i <= n,
                sum_x as int == sum_dim(vec@, i as int, 0),
                sum_y as int == sum_dim(vec@, i as int, 1),
                sum_z as int == sum_dim(vec@, i as int, 2),
                -100 * (i as int) <= sum_x as int <= 100 * (i as int),
                -100 * (i as int) <= sum_y as int <= 100 * (i as int),
                -100 * (i as int) <= sum_z as int <= 100 * (i as int),
            decreases n - i,
        {
            proof {
                lemma_sum_dim_step(vec@, i as int, 0);
                lemma_sum_dim_step(vec@, i as int, 1);
                lemma_sum_dim_step(vec@, i as int, 2);
            }
            sum_x += vec[3 * i] as i64;
            sum_y += vec[3 * i + 1] as i64;
            sum_z += vec[3 * i + 2] as i64;
            i += 1;
        }
        proof {
            assert(sum_x as int == sum_dim(vec@, n as int, 0));
            assert(sum_y as int == sum_dim(vec@, n as int, 1));
            assert(sum_z as int == sum_dim(vec@, n as int, 2));
            assert((sum_x == 0 && sum_y == 0 && sum_z == 0) == forces_equilibrium(vec@, n as int));
        }
        sum_x == 0 && sum_y == 0 && sum_z == 0
    }
}

}
