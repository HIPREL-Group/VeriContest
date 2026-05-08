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
        if reward_values.len() == 1 {
            return reward_values[0];
        }
        let mut vals = reward_values.clone();
        let mut a = 1usize;
        while a < vals.len() {
            let key = vals[a];
            let mut b = a;
            while b > 0 && vals[b - 1] > key {
                vals.set(b, vals[b - 1]);
                b -= 1;
            }
            vals.set(b, key);
            a += 1;
        }

        let mut reachable: Vec<bool> = vec![false; 4001];
        reachable[0] = true;

        let mut i = 0usize;
        while i < vals.len() {
            let r = vals[i] as usize;
            let mut s = 4000usize;
            loop {
                if reachable[s] && s < r {
                    let t = s + r;
                    if t <= 4000 {
                        reachable[t] = true;
                    }
                }
                if s == 0 {
                    break;
                }
                s -= 1;
            }
            i += 1;
        }

        let mut ans = 0usize;
        let mut x = 0usize;
        while x <= 4000 {
            if reachable[x] {
                ans = x;
            }
            if x == 4000 {
                break;
            }
            x += 1;
        }
        ans as i32
    }
}

}
