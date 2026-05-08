use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum_prefix(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        spec_sum_prefix(a, k - 1) + a[k - 1] as int
    }
}

pub open spec fn spec_min_odd_prefix(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 {
        101
    } else {
        let m = spec_min_odd_prefix(a, k - 1);
        let x = a[k - 1] as int;
        if x % 2 == 1 {
            if m < x {
                m
            } else {
                x
            }
        } else {
            m
        }
    }
}

pub open spec fn max_loving_petals_spec(a: Seq<i32>) -> int {
    let t = spec_sum_prefix(a, a.len() as int);
    let mo = spec_min_odd_prefix(a, a.len() as int);
    if t % 2 == 1 {
        t
    } else {
        if mo == 101 {
            0int
        } else {
            t - mo
        }
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn max_loving_petals(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 100,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100,
        ensures
            result as int == max_loving_petals_spec(a@),
    {
        let n = a.len();
        let mut total = 0i32;
        let mut min_odd = 101i32;
        let mut i = 0usize;
        while i < n {
            total = total + a[i];
            if a[i] % 2 == 1 {
                if a[i] < min_odd {
                    min_odd = a[i];
                }
            }
            i = i + 1;
        }
        let r = if total % 2 == 1 {
            total
        } else {
            if min_odd == 101 {
                0
            } else {
                total - min_odd
            }
        };
        r
    }
}

}
