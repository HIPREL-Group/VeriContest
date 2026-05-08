use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub closed spec fn is_sequential_digits(n: int) -> bool
        decreases n
    {
        if n < 10 {
            1 <= n && n <= 9
        } else {
            let last = n % 10;
            let rest = n / 10;
            let prev = rest % 10;
            2 <= last && last <= 9 && prev == last - 1 && Self::is_sequential_digits(rest)
        }
    }

    pub fn sequential_digits(low: i32, high: i32) -> (result: Vec<i32>)
        requires
            10 <= low <= high <= 1000000000,
        ensures
            forall|i: int| 0 <= i < result.len() ==> low <= #[trigger] result[i] <= high,
            forall|i: int| 0 <= i < result.len() ==> Self::is_sequential_digits(#[trigger] result[i] as int),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] < #[trigger] result[j],
            forall|x: int| (low <= x <= high && Self::is_sequential_digits(x)) ==> exists|k: int| 0 <= k < result.len() && #[trigger] result[k] == x as i32,
    {
    }
}

}
