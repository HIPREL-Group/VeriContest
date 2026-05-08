use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn vlad_beautiful(a: Vec<u32>, n: usize) -> (result: bool)
        requires
            1 <= n <= 200_000,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result == (
                (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] % 2 == 1)
                ||
                (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] % 2 == 0)
                ||
                (exists|j: int| 0 <= j < a.len() && #[trigger] a[j] % 2 == 1 &&
                    (forall|i: int| 0 <= i < a.len() && a[i] % 2 == 0 ==> #[trigger] a[i] > a[j]))
            ),
    {
        let mut min_even: u64 = u64::MAX;
        let mut min_odd: u64 = u64::MAX;
        let mut min_even_idx: usize = 0;
        let mut min_odd_idx: usize = 0;
        let mut i: usize = 0;
        while i < n {
            let v = a[i] as u64;
            if a[i] % 2 == 0 {
                if v < min_even {
                    min_even = v;
                    min_even_idx = i;
                }
            } else {
                if v < min_odd {
                    min_odd = v;
                    min_odd_idx = i;
                }
            }
            i += 1;
        }
        if min_even == u64::MAX {
            true
        } else if min_odd == u64::MAX {
            true
        } else {
            let res = min_odd < min_even;
            res
        }
    }
}

}
