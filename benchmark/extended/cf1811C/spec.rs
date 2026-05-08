use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

impl Solution {
    pub fn restore_array(n: usize, b: Vec<i64>) -> (result: Vec<i64>)
        requires
            n >= 2,
            b.len() == n - 1,
            forall|i: int| 0 <= i < n - 1 ==> 0 <= #[trigger] b[i] <= 1_000_000_000,
            forall|i: int| 1 <= i < n as int - 2 ==> #[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1],
        ensures
            result.len() == n,
            forall|i: int| 0 <= i < n as int ==> #[trigger] result[i] >= 0,
            forall|i: int|
                0 <= i < n - 1 ==> spec_max(
                    #[trigger] result[i] as int,
                    result[i + 1] as int,
                ) == b[i] as int,
    {
    }
}

}
