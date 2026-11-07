use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;



pub open spec fn apply_one(sum: int, ce: int, co: int, qtype: u32, x: u32) -> (int, int, int) {
    if qtype == 0u32 {
        let new_sum = sum + ce * (x as int);
        if x % 2 == 0 {
            (new_sum, ce, co)
        } else {
            (new_sum, 0, co + ce)
        }
    } else {
        let new_sum = sum + co * (x as int);
        if x % 2 == 0 {
            (new_sum, ce, co)
        } else {
            (new_sum, ce + co, 0)
        }
    }
}

pub open spec fn state_after(s0: int, ce0: int, co0: int, qtypes: Seq<u32>, qxs: Seq<u32>, k: int) -> (int, int, int)
    recommends 0 <= k <= qtypes.len(), qtypes.len() == qxs.len(),
    decreases k,
{
    if k <= 0 {
        (s0, ce0, co0)
    } else {
        let prev = state_after(s0, ce0, co0, qtypes, qxs, k - 1);
        apply_one(prev.0, prev.1, prev.2, qtypes[k - 1], qxs[k - 1])
    }
}

pub open spec fn initial_sum(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 { 0int } else { a[0] as int + initial_sum(a.subrange(1, a.len() as int)) }
}

pub open spec fn initial_even_count(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 { 0int }
    else {
        let rest = initial_even_count(a.subrange(1, a.len() as int));
        if a[0] % 2 == 0 { rest + 1 } else { rest }
    }
}

pub open spec fn initial_odd_count(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 { 0int }
    else {
        let rest = initial_odd_count(a.subrange(1, a.len() as int));
        if a[0] % 2 == 1 { rest + 1 } else { rest }
    }
}

impl Solution {
    pub fn even_odd_sums(a: Vec<u32>, n: usize, qtypes: Vec<u32>, qxs: Vec<u32>, q: usize) -> (result: Vec<i64>)
        requires
            1 <= n <= 100_000,
            1 <= q <= 100_000,
            a.len() == n,
            qtypes.len() == q,
            qxs.len() == q,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < qtypes.len() ==> #[trigger] qtypes[i] <= 1,
            forall|i: int| 0 <= i < qxs.len() ==> 1 <= #[trigger] qxs[i] <= 10_000,
        ensures
            result.len() == q,
            forall|k: int| 0 <= k < q ==> #[trigger] result[k] as int == state_after(
                initial_sum(a@), initial_even_count(a@), initial_odd_count(a@),
                qtypes@, qxs@, k + 1
            ).0,
    {
    }
}

}
