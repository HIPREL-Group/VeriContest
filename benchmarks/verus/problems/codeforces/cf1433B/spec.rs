use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn first_one_idx(a: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        -1
    } else {
        let r = first_one_idx(a, k - 1);
        if r != -1 {
            r
        } else if a[k - 1] == 1u8 {
            k - 1
        } else {
            -1
        }
    }
}

pub open spec fn last_one_idx(a: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        -1
    } else if a[k - 1] == 1u8 {
        k - 1
    } else {
        last_one_idx(a, k - 1)
    }
}

pub open spec fn count_zeros_prefix(a: Seq<u8>, lo: int, k: int) -> int
    decreases k - lo,
{
    if k <= lo {
        0
    } else {
        let prev = count_zeros_prefix(a, lo, k - 1);
        if a[k - 1] == 0u8 { prev + 1 } else { prev }
    }
}

impl Solution {
    pub fn min_moves_books(n: usize, a: Vec<u8>) -> (result: usize)
        requires
            1 <= n <= 50,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1u8,
            exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 1u8,
        ensures
            result as int == count_zeros_prefix(a@, first_one_idx(a@, n as int), last_one_idx(a@, n as int) + 1),
    {
    }
}

}
