use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_lucky_digits(digits: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < digits.len() ==> (#[trigger] digits[i] == 4u8 || digits[i] == 7u8)
}

pub open spec fn sum_range(digits: Seq<u8>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0int
    } else {
        digits[lo] as int + sum_range(digits, lo + 1, hi)
    }
}

impl Solution {
    pub fn is_lucky_ticket(n: usize, digits: Vec<u8>) -> (res: bool)
        requires
            2 <= n <= 50,
            n % 2 == 0,
            digits.len() == n,
            forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] <= 9u8,
        ensures
            res == (all_lucky_digits(digits@) && sum_range(digits@, 0, (n / 2) as int) == sum_range(digits@, (n / 2) as int, n as int)),
    {
    }
}

}
