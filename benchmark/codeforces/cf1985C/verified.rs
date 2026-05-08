use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum(a: Seq<u64>, end: int) -> int
    recommends
        0 <= end <= a.len(),
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        prefix_sum(a, end - 1) + a[end - 1] as int
    }
}

pub open spec fn prefix_max(a: Seq<u64>, end: int) -> int
    recommends
        1 <= end <= a.len(),
    decreases end,
{
    if end <= 1 {
        a[0] as int
    } else {
        let prev = prefix_max(a, end - 1);
        let v = a[end - 1] as int;
        if v > prev { v } else { prev }
    }
}

pub open spec fn count_good_prefixes(a: Seq<u64>, end: int) -> int
    recommends
        0 <= end <= a.len(),
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        let prev = count_good_prefixes(a, end - 1);
        let s = prefix_sum(a, end);
        let m = prefix_max(a, end);
        if 2 * m == s {
            prev + 1
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn count_good_prefixes_fn(a: Vec<u64>) -> (result: usize)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1_000_000_000u64,
        ensures
            result as int == count_good_prefixes(a@, a.len() as int),
    {
        let mut sum: u64 = 0;
        let mut max_val: u64 = 0;
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                a.len() <= 200_000,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] <= 1_000_000_000u64,
                sum as int == prefix_sum(a@, i as int),
                sum as int <= (i as int) * 1_000_000_000,
                i == 0 ==> max_val == 0,
                i > 0 ==> max_val as int == prefix_max(a@, i as int),
                max_val <= 1_000_000_000u64,
                count as int == count_good_prefixes(a@, i as int),
                count <= i,
            decreases a.len() - i,
        {
            proof {
                reveal_with_fuel(prefix_sum, 2);
                reveal_with_fuel(prefix_max, 2);
                reveal_with_fuel(count_good_prefixes, 2);
                assert(a[i as int] <= 1_000_000_000u64);
                assert((i as int + 1) * 1_000_000_000 == (i as int) * 1_000_000_000 + 1_000_000_000) by(nonlinear_arith);
            }
            let ai = a[i];
            sum = sum + ai;
            if ai > max_val {
                max_val = ai;
            }
            if 2 * max_val == sum {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}

}
