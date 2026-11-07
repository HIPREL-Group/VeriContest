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

impl Solution {
    pub fn min_costs(cost: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= cost.len() <= 100,
            forall |i: int| 0 <= i < cost.len() ==> 1 <= #[trigger] cost[i] <= 100,
        ensures
            answer.len() == cost.len(),
            forall |i: int| 0 <= i < cost.len() ==> #[trigger] answer[i] == spec_prefix_min(cost@, i + 1),
    {
    }
}

} 
