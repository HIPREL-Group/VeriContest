use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn steps_between(n: int, from: int, to: int) -> int
    recommends
        1 <= n,
        1 <= from <= n,
        1 <= to <= n,
{
    if to >= from {
        to - from
    } else {
        n - from + to
    }
}

pub open spec fn total_steps_spec(n: int, targets: Seq<i64>, start: int, idx: int) -> int
    recommends
        1 <= n,
        0 <= idx <= targets.len(),
        1 <= start <= n,
        forall|i: int| 0 <= i < targets.len() ==> 1 <= #[trigger] targets[i] as int <= n,
    decreases
        targets.len() as int - idx,
{
    if idx >= targets.len() {
        0
    } else {
        steps_between(n, start, targets[idx] as int)
            + total_steps_spec(n, targets, targets[idx] as int, idx + 1)
    }
}

impl Solution {
    pub fn total_steps(n: i64, targets: Vec<i64>) -> (result: i64)
        requires
            1 <= n as int <= 100_000,
            targets.len() as int <= 100_000,
            forall|i: int| 0 <= i < targets.len() ==> 1 <= #[trigger] targets[i] as int <= n as int,
        ensures
            result as int == total_steps_spec(n as int, targets@, 1, 0),
    {
    }
}

}
