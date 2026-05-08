use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_last_digit_of_multiple(k: int, m: int) -> int {
    (k * m) % 10
}

pub open spec fn spec_cycle_digit_sum(m: int) -> int {
    spec_last_digit_of_multiple(1, m) + spec_last_digit_of_multiple(2, m)
        + spec_last_digit_of_multiple(3, m) + spec_last_digit_of_multiple(4, m)
        + spec_last_digit_of_multiple(5, m) + spec_last_digit_of_multiple(6, m)
        + spec_last_digit_of_multiple(7, m) + spec_last_digit_of_multiple(8, m)
        + spec_last_digit_of_multiple(9, m) + spec_last_digit_of_multiple(10, m)
}

pub open spec fn spec_prefix_digit_sum(rem: int, m: int) -> int
    decreases rem
{
    if rem <= 0 {
        0
    } else {
        spec_prefix_digit_sum(rem - 1, m) + spec_last_digit_of_multiple(rem, m)
    }
}

pub open spec fn spec_book_reading_sum(n: int, m: int) -> int
    recommends
        n >= 1,
        m >= 1,
{
    let t = n / m;
    (t / 10) * spec_cycle_digit_sum(m) + spec_prefix_digit_sum(t % 10, m)
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn book_reading_digit_sum(n: u64, m: u64) -> (r: u64)
        requires
            1 <= n <= 10_000_000_000_000_000,
            1 <= m <= 10_000_000_000_000_000,
        ensures
            (r as int) == spec_book_reading_sum(n as int, m as int),
    {
        let t = n / m;
        let m10 = m % 10;
        let mut cycle_sum: u64 = 0;
        let mut i: u64 = 1;
        while i <= 10 {
            let imod32 = (i % 10) as u32;
            let m1032 = m10 as u32;
            let d = ((imod32 * m1032) % 10) as u64;
            cycle_sum = cycle_sum + d;
            i = i + 1;
        }
        let full = t / 10;
        let rem = t % 10;
        let mut partial: u64 = 0;
        i = 1;
        while i <= rem {
            let imod32 = (i % 10) as u32;
            let m1032 = m10 as u32;
            let d = ((imod32 * m1032) % 10) as u64;
            partial = partial + d;
            i = i + 1;
        }
        let res = full * cycle_sum + partial;
        res
    }
}

}
