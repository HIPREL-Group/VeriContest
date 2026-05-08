use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum_entries(entries: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_entries(entries, end - 1) + entries[end - 1] as int
    }
}

pub open spec fn prefix_sum_exits(exits: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_exits(exits, end - 1) + exits[end - 1] as int
    }
}

pub open spec fn prefix_passengers(entries: Seq<i32>, exits: Seq<i32>, end: int) -> int {
    prefix_sum_entries(entries, end) - prefix_sum_exits(exits, end)
}

pub open spec fn max_prefix_passengers(entries: Seq<i32>, exits: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        let prev = max_prefix_passengers(entries, exits, n - 1);
        let curr = prefix_passengers(entries, exits, n);
        if curr > prev {
            curr
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn max_passengers(exits: Vec<i32>, entries: Vec<i32>) -> (result: i32)
        requires
            2 <= exits.len() <= 1000,
            exits.len() == entries.len(),
            forall|i: int| 0 <= i < exits.len() ==> 0 <= #[trigger] exits[i] <= 1000,
            forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i] <= 1000,
            exits[0] == 0,
            entries[exits.len() - 1] == 0,
            forall|i: int| 0 <= i < exits.len() ==>
                #[trigger] exits@[i] as int <= prefix_passengers(entries@, exits@, i),
        ensures
            result as int == max_prefix_passengers(entries@, exits@, exits.len() as int),
            forall|i: int| 0 <= i <= exits.len() as int ==>
                prefix_passengers(entries@, exits@, i) <= result as int,
            exists|i: int| 0 <= i <= exits.len() as int
                && prefix_passengers(entries@, exits@, i) == result as int,
    {
        let n = exits.len();
        let mut max_val = 0i32;
        let mut current = 0i32;
        let mut i = 0usize;
        while i < n {
            current = current - exits[i] + entries[i];
            if current > max_val {
                max_val = current;
            }
            i += 1;
        }
        max_val
    }
}

}
