use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_power10(p: int) -> bool
        decreases p,
    {
        if p < 1 {
            false
        } else if p == 1 {
            true
        } else {
            p % 10 == 0 && Self::is_power10(p / 10)
        }
    }

    pub open spec fn is_base10_component(x: int) -> bool {
        exists|d: int, p: int| 1 <= d <= 9 && p >= 1 && Self::is_power10(p) && x == #[trigger] (d * p)
    }

    pub open spec fn count_nonzero_digits(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_nonzero_digits(n / 10) + if n % 10 == 0 { 0int } else { 1int }
        }
    }

    pub open spec fn spec_sum_prefix(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::spec_sum_prefix(s, end - 1) + s[end - 1] as int
        }
    }

    pub fn decimal_representation(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result.len() == Self::count_nonzero_digits(n as int),
            Self::spec_sum_prefix(result@, result.len() as int) == n,
            forall|i: int| 0 <= i < result.len() ==> Self::is_base10_component(#[trigger] result[i] as int),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] > #[trigger] result[j],
    {
    }
}

}
