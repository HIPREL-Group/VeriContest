use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map(|_idx: int, x: i32| x as int)
}























pub open spec fn count_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        count_above(s.drop_last(), t)
            + if s.last() > t { s.last() - t } else { 0 }
    }
}

pub open spec fn value_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        value_above(s.drop_last(), t)
            + if s.last() > t { (s.last() + t + 1) * (s.last() - t) / 2 } else { 0 }
    }
}

impl Solution {
    pub fn max_profit(inventory: Vec<i32>, orders: i32) -> (result: i32)
        requires
            1 <= inventory.len() <= 100_000,
            forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
            1 <= orders <= 1_000_000_000,
            orders as int <= count_above(to_int_seq(inventory@), 0),
        ensures
            exists |t: int| {
                &&& 0 <= t
                &&& count_above(to_int_seq(inventory@), t) <= orders as int
                &&& (t == 0 || count_above(to_int_seq(inventory@), t - 1) > orders as int)
                &&& result as int == (value_above(to_int_seq(inventory@), t)
                    + (orders as int - count_above(to_int_seq(inventory@), t)) * t)
                    % 1_000_000_007
            },
    {
    }
}

}
