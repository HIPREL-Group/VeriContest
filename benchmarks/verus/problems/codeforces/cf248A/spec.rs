use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_ones(seq: Seq<u8>, n: int) -> int
    recommends
        0 <= n <= seq.len(),
    decreases n,
{
    if n <= 0 {
        0int
    } else {
        let prev = count_ones(seq, n - 1);
        if seq[n - 1] == 1u8 { prev + 1 } else { prev }
    }
}

pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

impl Solution {
    pub fn min_seconds(left: Vec<u8>, right: Vec<u8>, n: usize) -> (result: usize)
        requires
            2 <= n <= 10000,
            left.len() == n,
            right.len() == n,
            forall|i: int| 0 <= i < left.len() ==> #[trigger] left[i] <= 1u8,
            forall|i: int| 0 <= i < right.len() ==> #[trigger] right[i] <= 1u8,
        ensures
            result as int == min_int(count_ones(left@, n as int), n as int - count_ones(left@, n as int))
                + min_int(count_ones(right@, n as int), n as int - count_ones(right@, n as int)),
    {
    }
}

}
