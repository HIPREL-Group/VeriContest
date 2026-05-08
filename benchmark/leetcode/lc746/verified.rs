use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_cost_to_reach(cost: Seq<i32>, i: int) -> int 
        decreases i
    {
        if i == 0 {
            cost[0] as int
        } else if i == 1 {
            cost[1] as int
        } else if 2 <= i < cost.len() {
            (cost[i] as int) + if Self::min_cost_to_reach(cost, i-1) < Self::min_cost_to_reach(cost, i-2) {
                Self::min_cost_to_reach(cost, i-1)
            } else {
                Self::min_cost_to_reach(cost, i-2)
            }
        } else {
            0
        }
    }

    pub open spec fn min_cost_climbing_stairs_spec(cost: Seq<i32>) -> int
    {
        let n = cost.len();
        if Self::min_cost_to_reach(cost, (n - 1) as int) < Self::min_cost_to_reach(cost, (n - 2) as int) {
            Self::min_cost_to_reach(cost, (n - 1) as int)
        } else {
            Self::min_cost_to_reach(cost, (n - 2) as int)
        }
    }

    proof fn min_cost_bounds(cost: Seq<i32>, i: int)
        requires
            2 <= cost.len() <= 1000,
            forall |j: int| 0 <= j < cost.len() ==> 0 <= #[trigger] cost[j] <= 999,
            0 <= i < cost.len(),
        ensures
            0 <= Self::min_cost_to_reach(cost, i) <= 999 * (i + 1),
        decreases i
    {
        if i >= 2 {
            Self::min_cost_bounds(cost, i - 1);
            Self::min_cost_bounds(cost, i - 2);
        }
    }

    pub fn min_cost_climbing_stairs(cost: Vec<i32>) -> (res: i32) 
        requires 
            2 <= cost.len() <= 1000, 
            forall |i: int| 0 <= i < cost.len() ==> 0 <= #[trigger] cost[i] <= 999, 
        ensures 
            res == Self::min_cost_climbing_stairs_spec(cost@)
    {
        let n = cost.len();
        let (mut a, mut b) = (cost[0], cost[1]);
        for i in 2..n 
            invariant
                2 <= cost.len() <= 1000, 
                forall |i: int| 0 <= i < cost.len() ==> 0 <= #[trigger] cost[i] <= 999, 
                n == cost.len(),
                2 <= i <= n,
                forall |j: int| 0 <= j < cost@.len() ==> 0 <= #[trigger] cost@[j] <= 999,
                a as int == Self::min_cost_to_reach(cost@, (i - 2) as int),
                b as int == Self::min_cost_to_reach(cost@, (i - 1) as int),
                0 <= a <= 999000,
                0 <= b <= 999000,
        { 
            proof {
                Self::min_cost_bounds(cost@, i as int);
                Self::min_cost_bounds(cost@, (i - 1) as int);
                Self::min_cost_bounds(cost@, (i - 2) as int);
            }

            let c = cost[i] + if a < b { a } else { b };
            a = b;
            b = c;
        }
        if a < b { a } else { b }
    }
}

}