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
        let mut all_lucky = true;
        let mut i: usize = 0;
        while i < n {
            if digits[i] != 4u8 && digits[i] != 7u8 {
                all_lucky = false;
            }
            i += 1;
        }
        if !all_lucky {
            return false;
        }
        let half = n / 2;
        let mut sum1: u64 = 0;
        let mut sum2: u64 = 0;
        let mut j: usize = 0;
        while j < half {
            sum1 = sum1 + digits[j] as u64;
            j += 1;
        }
        let mut k: usize = half;
        while k < n {
            sum2 = sum2 + digits[k] as u64;
            k += 1;
        }
        sum1 == sum2
    }
}

}
