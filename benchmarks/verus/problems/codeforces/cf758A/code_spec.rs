use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_max_of(a: Seq<i32>, n: int) -> int
    recommends 1 <= n <= a.len(),
    decreases n,
{
    if n <= 1 {
        a[0] as int
    } else {
        let m = spec_max_of(a, n - 1);
        if (a[n - 1] as int) > m {
            a[n - 1] as int
        } else {
            m
        }
    }
}

pub open spec fn spec_gap_sum(a: Seq<i32>, n: int, maxv: int) -> int
    recommends 0 <= n <= a.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_gap_sum(a, n - 1, maxv) + (maxv - (a[n - 1] as int))
    }
}

pub open spec fn spec_holiday_equality(a: Seq<i32>, n: int) -> int
    recommends 1 <= n <= a.len(),
{
    let m = spec_max_of(a, n);
    spec_gap_sum(a, n, m)
}

impl Solution {
    pub fn holiday_equality_burles(n: usize, a: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 100,
            n == a.len(),
            forall|k: int|
                0 <= k < n as int ==> 0 <= #[trigger] a[k] <= 1_000_000,
        ensures
            res as int == spec_holiday_equality(a@, n as int),
    {
        let mut maxv = a[0];
        let mut i = 1usize;
        while i < n {
            if a[i] > maxv {
                maxv = a[i];
            }
            i += 1;
        }
        let mut sum = 0i32;
        let mut j = 0usize;
        while j < n {
            sum += maxv - a[j];
            j += 1;
        }
        sum
    }
}

}
