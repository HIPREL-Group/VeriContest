use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_min(cost: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 1 {
        cost[0] as int
    } else if (cost[k - 1] as int) < spec_prefix_min(cost, k - 1) {
        cost[k - 1] as int
    } else {
        spec_prefix_min(cost, k - 1)
    }
}

proof fn lemma_prefix_min_bounds(cost: Seq<i32>, k: int)
    requires
        1 <= k <= cost.len(),
        forall |i: int| 0 <= i < cost.len() ==> 1 <= #[trigger] cost[i] <= 100,
    ensures
        1 <= spec_prefix_min(cost, k) <= 100,
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_prefix_min_bounds(cost, k - 1);
    }
}

impl Solution {
    pub fn min_costs(cost: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= cost.len() <= 100,
            forall |i: int| 0 <= i < cost.len() ==> 1 <= #[trigger] cost[i] <= 100,
        ensures
            answer.len() == cost.len(),
            forall |i: int| 0 <= i < cost.len() ==> #[trigger] answer[i] == spec_prefix_min(cost@, i + 1),
    {
        let n = cost.len();
        let mut answer: Vec<i32> = vec![0i32; n];
        let mut min_cost: i32 = cost[0];
        answer.set(0, min_cost);
        assert(answer[0int] == spec_prefix_min(cost@, 1int));
        let mut i: usize = 1;
        while i < n
            invariant
                n == cost.len(),
                1 <= n <= 100,
                forall |j: int| 0 <= j < cost.len() ==> 1 <= #[trigger] cost[j] <= 100,
                1 <= i <= n,
                answer.len() == n,
                min_cost as int == spec_prefix_min(cost@, i as int),
                1 <= min_cost <= 100,
                forall |j: int| 0 <= j < i ==> #[trigger] answer[j] == spec_prefix_min(cost@, j + 1),
            decreases n - i,
        {
            if cost[i] < min_cost {
                min_cost = cost[i];
            }
            assert(min_cost as int == spec_prefix_min(cost@, (i + 1) as int));
            answer.set(i, min_cost);
            i += 1;
        }
        answer
    }
}

} 
