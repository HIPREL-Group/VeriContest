use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_range(a: Seq<u32>, l: int, r: int) -> int
    recommends 0 <= l <= r <= a.len(),
    decreases r - l,
{
    if l >= r { 0int }
    else { a[l] as int + sum_range(a, l + 1, r) }
}

impl Solution {
    pub fn odd_queries(
        a: Vec<u32>,
        n: usize,
        ls: Vec<u32>,
        rs: Vec<u32>,
        ks: Vec<u32>,
        q: usize,
    ) -> (result: Vec<bool>)
        requires
            1 <= n <= 200_000,
            1 <= q <= 200_000,
            a.len() == n,
            ls.len() == q,
            rs.len() == q,
            ks.len() == q,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] && ls[i] as int <= rs[i] as int && rs[i] as int <= n as int,
            forall|i: int| 0 <= i < rs.len() ==> 1 <= #[trigger] rs[i] && rs[i] as int <= n as int,
            forall|i: int| 0 <= i < ks.len() ==> 1 <= #[trigger] ks[i] <= 1_000_000_000,
        ensures
            result.len() == q,
            forall|i: int| 0 <= i < q ==> #[trigger] result[i] == (
                (sum_range(a@, 0, ls[i] as int - 1) +
                 ks[i] as int * (rs[i] as int - ls[i] as int + 1) +
                 sum_range(a@, rs[i] as int, n as int)) % 2 == 1
            ),
    {
    }
}

}
