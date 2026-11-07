use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_range(a: Seq<i32>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi < a.len(),
    decreases
        hi - lo,
{
    if lo < hi {
        let m = min_range(a, lo + 1, hi);
        if (a[lo] as int) < m {
            a[lo] as int
        } else {
            m
        }
    } else {
        a[lo] as int
    }
}

pub open spec fn has_smaller_to_right(a: Seq<i32>, i: int) -> bool {
    exists |j: int| i < j < a.len() && (#[trigger] a[j]) < (#[trigger] a[i])
}

pub open spec fn count_bad_recursive(a: Seq<i32>, start: int) -> int
    recommends
        0 <= start <= a.len(),
    decreases
        a.len() - start,
{
    if start >= a.len() {
        0
    } else {
        count_bad_recursive(a, start + 1) + if has_smaller_to_right(a, start) {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn count_bad_prices_spec(a: Seq<i32>) -> int {
    count_bad_recursive(a, 0)
}

impl Solution {
    pub fn count_bad_prices(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 150_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= (#[trigger] a[k]) <= 1_000_000,
        ensures
            result == count_bad_prices_spec(a@),
    {
        let n = a.len();
        if n <= 1 {
            return 0;
        }
        let mut cnt: i32 = 0;
        let mut cur_min = a[n - 1];
        let mut i: usize = n - 2;
        loop {
            if a[i] > cur_min {
                cnt = cnt + 1;
            }
            if a[i] < cur_min {
                cur_min = a[i];
            }
            if i == 0 {
                break;
            }
            i = i - 1;
        }
        cnt
    }
}

}
