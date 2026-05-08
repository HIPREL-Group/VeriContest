use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn filtered_prefix(order: Seq<i32>, friends: Seq<i32>, k: nat) -> Seq<i32>
        decreases k,
    {
        if k == 0 {
            seq![]
        } else {
            let prev = Solution::filtered_prefix(order, friends, (k - 1) as nat);
            if friends.contains(order[(k - 1) as int]) {
                prev.push(order[(k - 1) as int])
            } else {
                prev
            }
        }
    }

    pub open spec fn finishing_order(order: Seq<i32>, friends: Seq<i32>) -> Seq<i32>
    {
        Solution::filtered_prefix(order, friends, order.len())
    }

    pub fn recover_order(order: Vec<i32>, friends: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= order.len() <= 100,
            forall |i: int| 0 <= i < order.len() ==> 1 <= #[trigger] order[i] <= order.len() as i32,
            forall |i: int, j: int| 0 <= i < j < order.len() ==> order[i] != order[j],
            forall |id: int| 1 <= id <= order.len() ==> #[trigger] order@.contains(id as i32),
            1 <= friends.len() <= 8,
            friends.len() <= order.len(),
            forall |i: int| 0 <= i < friends.len() ==> 1 <= #[trigger] friends[i] <= order.len() as i32,
            forall |i: int, j: int| 0 <= i < j < friends.len() ==> friends[i] < friends[j],
            forall |i: int| 0 <= i < friends.len() ==> order@.contains(#[trigger] friends[i]),
        ensures
            result@ == Solution::finishing_order(order@, friends@),
    {
    }
}

}
