use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn buy_for_index(tickets: Seq<i32>, k: int, i: int) -> int
        recommends
            0 <= k < tickets.len(),
            0 <= i < tickets.len(),
            forall |j: int| 0 <= j < tickets.len() ==> 1 <= #[trigger] tickets[j] <= 100,
    {
        if i <= k {
            Self::min2(tickets[i] as int, tickets[k] as int)
        } else {
            Self::min2(tickets[i] as int, tickets[k] as int - 1)
        }
    }

    pub open spec fn total_upto(tickets: Seq<i32>, k: int, upto: int) -> int
        recommends
            0 <= k < tickets.len(),
            0 <= upto <= tickets.len(),
            forall |j: int| 0 <= j < tickets.len() ==> 1 <= #[trigger] tickets[j] <= 100,
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::total_upto(tickets, k, upto - 1) + Self::buy_for_index(tickets, k, upto - 1)
        }
    }

    pub fn time_required_to_buy(tickets: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= tickets.len() <= 100,
            0 <= k < tickets.len(),
            forall |j: int| 0 <= j < tickets.len() ==> 1 <= #[trigger] tickets[j] <= 100,
        ensures
            result as int == Self::total_upto(tickets@, k as int, tickets.len() as int),
    {
    }
}

}
