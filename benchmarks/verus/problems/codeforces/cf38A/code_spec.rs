use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_range(d: Seq<u32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo || lo < 0 || hi > d.len() {
        0int
    } else {
        d[lo] as int + sum_range(d, lo + 1, hi)
    }
}

impl Solution {
    pub fn years_needed(n: usize, d: Vec<u32>, a: usize, b: usize) -> (result: u32)
        requires
            2 <= n <= 100,
            d.len() == n - 1,
            forall|i: int| 0 <= i < d.len() ==> 1 <= #[trigger] d[i] as int <= 100,
            1 <= a < b <= n,
        ensures
            result as int == sum_range(d@, (a - 1) as int, (b - 1) as int),
    {
        let mut sum: u32 = 0;
        let mut i: usize = a - 1;
        let lo: usize = a - 1;
        let hi: usize = b - 1;
        while i < hi {
            sum += d[i];
            i += 1;
        }
        sum
    }
}

}
