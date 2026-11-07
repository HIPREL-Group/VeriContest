use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn process(events: Seq<i32>, idx: int) -> (int, int)
    decreases idx,
{
    if idx <= 0 {
        (0int, 0int)
    } else {
        let (officers, untreated) = process(events, idx - 1);
        let e = events[idx - 1] as int;
        if e == -1 {
            if officers > 0 {
                (officers - 1, untreated)
            } else {
                (officers, untreated + 1)
            }
        } else {
            (officers + e, untreated)
        }
    }
}

impl Solution {
    pub fn count_untreated(n: usize, events: Vec<i32>) -> (result: u64)
        requires
            1 <= n <= 100000,
            events.len() == n,
            forall|i: int| 0 <= i < events.len() ==> #[trigger] events[i] as int == -1 || (1 <= events[i] as int <= 10),
        ensures
            result as int == process(events@, n as int).1,
    {
    }
}

}
