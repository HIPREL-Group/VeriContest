use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(gas: Seq<i32>, cost: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(gas, cost, end - 1) + (gas[end - 1] as int) - (cost[end - 1] as int)
        }
    }

    pub open spec fn can_complete_from(gas: Seq<i32>, cost: Seq<i32>, start: int) -> bool
    {
        let n = gas.len() as int;
        forall|k: int| 1 <= k <= n ==> #[trigger] Self::route_balance(gas, cost, start, k) >= 0
    }

    pub open spec fn route_balance(gas: Seq<i32>, cost: Seq<i32>, start: int, k: int) -> int
    {
        let n = gas.len() as int;
        if start + k <= n {
            Self::prefix_sum(gas, cost, start + k) - Self::prefix_sum(gas, cost, start)
        } else {
            Self::prefix_sum(gas, cost, n) - Self::prefix_sum(gas, cost, start)
                + Self::prefix_sum(gas, cost, start + k - n)
        }
    }

    pub fn can_complete_circuit(gas: Vec<i32>, cost: Vec<i32>) -> (result: i32)
        requires
            gas.len() == cost.len(),
            1 <= gas.len() <= 100_000,
            forall|i: int| 0 <= i < gas.len() ==> 0 <= #[trigger] gas[i] <= 10_000,
            forall|i: int| 0 <= i < cost.len() ==> 0 <= #[trigger] cost[i] <= 10_000,
        ensures
            -1 <= result < gas.len() as i32,
            result == -1 ==> !(exists|s: int| 0 <= s < gas.len() && Self::can_complete_from(gas@, cost@, s)),
            result != -1 ==> Self::can_complete_from(gas@, cost@, result as int),
    {
        
    }
}

} 
