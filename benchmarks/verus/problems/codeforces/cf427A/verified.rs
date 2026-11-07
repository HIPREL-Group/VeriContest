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

proof fn lemma_process_bounds(events: Seq<i32>, idx: int)
    requires
        0 <= idx <= events.len(),
        forall|i: int| 0 <= i < events.len() ==> #[trigger] events[i] as int == -1 || (1 <= events[i] as int <= 10),
    ensures
        0 <= process(events, idx).0 <= 10 * idx,
        0 <= process(events, idx).1 <= idx,
    decreases idx,
{
    if idx > 0 {
        lemma_process_bounds(events, idx - 1);
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
        let mut officers: u64 = 0;
        let mut untreated: u64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n <= 100000,
                events.len() == n,
                forall|j: int| 0 <= j < events.len() ==> #[trigger] events[j] as int == -1 || (1 <= events[j] as int <= 10),
                officers as int == process(events@, i as int).0,
                untreated as int == process(events@, i as int).1,
                officers <= 10 * (i as u64),
                untreated <= i as u64,
            decreases n - i,
        {
            proof {
                lemma_process_bounds(events@, i as int);
            }
            let e = events[i];
            if e == -1 {
                if officers > 0 {
                    officers = officers - 1;
                } else {
                    untreated = untreated + 1;
                }
            } else {
                officers = officers + (e as u64);
            }
            i += 1;
        }
        untreated
    }
}

}
