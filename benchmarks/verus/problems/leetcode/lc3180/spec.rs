use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn reward_order_sum(reward_values: Seq<i32>, order: Seq<int>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::reward_order_sum(reward_values, order, end - 1)
                + reward_values[order[end - 1]] as int
        }
    }

    pub open spec fn valid_reward_order(reward_values: Seq<i32>, order: Seq<int>) -> bool {
        &&& order.len() <= reward_values.len()
        &&& forall |i: int| 0 <= i < order.len()
            ==> 0 <= #[trigger] order[i] < reward_values.len()
        &&& forall |i: int, j: int| 0 <= i < j < order.len()
            ==> #[trigger] order[i] != #[trigger] order[j]
        &&& forall |i: int| 0 <= i < order.len()
            ==> reward_values[#[trigger] order[i]] as int
                > Self::reward_order_sum(reward_values, order, i)
    }

    pub open spec fn reward_path_ok(reward_values: Seq<i32>, path: Seq<int>) -> bool {
        &&& 1 <= path.len()
        &&& path[0] == 0
        &&& forall |s: int| 0 <= s < path.len() ==> 0 <= #[trigger] path[s] <= 4000
        &&& forall |s: int| 0 <= s < path.len() - 1 ==> exists |i: int|
            0 <= i < reward_values.len()
                && #[trigger] path[s] < #[trigger] reward_values[i] as int
                && path[s + 1] == path[s] + reward_values[i] as int
    }

    pub open spec fn reward_reachable(reward_values: Seq<i32>, total: int) -> bool {
        exists |path: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, path)
            && path[path.len() - 1] == total
    }

    pub open spec fn max_total_reward_spec(reward_values: Seq<i32>, result: int) -> bool {
        &&& 1 <= reward_values.len() <= 2000
        &&& forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000
        &&& 0 <= result <= 4000
        &&& Self::reward_reachable(reward_values, result)
        &&& forall |candidate: int| Self::reward_reachable(reward_values, candidate) ==> candidate <= result
    }

    pub fn max_total_reward(reward_values: Vec<i32>) -> (result: i32)
        requires
            1 <= reward_values.len() <= 2000,
            forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000,
        ensures
            Self::max_total_reward_spec(reward_values@, result as int),
    {
    }
}

}
