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

proof fn lemma_sum_range_bound(d: Seq<u32>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= d.len(),
        forall|i: int| 0 <= i < d.len() ==> 1 <= #[trigger] d[i] as int <= 100,
    ensures
        0 <= sum_range(d, lo, hi) <= (hi - lo) * 100,
    decreases hi - lo,
{
    if lo < hi {
        lemma_sum_range_bound(d, lo + 1, hi);
    }
}

proof fn lemma_sum_range_step(d: Seq<u32>, lo: int, hi: int)
    requires
        0 <= lo <= hi < d.len(),
    ensures
        sum_range(d, lo, hi + 1) == sum_range(d, lo, hi) + d[hi] as int,
    decreases hi - lo,
{
    if lo == hi {
        assert(sum_range(d, lo, hi + 1) == d[lo] as int + sum_range(d, lo + 1, hi + 1));
        assert(sum_range(d, lo + 1, hi + 1) == 0);
        assert(sum_range(d, lo, hi) == 0);
    } else {
        lemma_sum_range_step(d, lo + 1, hi);
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
        while i < hi
            invariant
                lo == a - 1,
                hi == b - 1,
                lo <= i <= hi,
                hi <= d.len(),
                hi - lo <= 99,
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] as int <= 100,
                sum as int == sum_range(d@, lo as int, i as int),
                0 <= sum as int <= (i - lo) * 100,
            decreases hi - i,
        {
            proof {
                lemma_sum_range_step(d@, lo as int, i as int);
                lemma_sum_range_bound(d@, lo as int, hi as int);
            }
            sum += d[i];
            i += 1;
        }
        sum
    }
}

}
