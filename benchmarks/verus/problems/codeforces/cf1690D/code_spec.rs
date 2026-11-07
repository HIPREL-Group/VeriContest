use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_range(s: Seq<i64>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= s.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            s[l] as int + Self::sum_range(s, l + 1, r)
        }
    }

    pub open spec fn min_white_windows(s: Seq<i64>, k: int, processed: int) -> int
        recommends
            1 <= k <= s.len(),
            0 <= processed <= s.len() - k + 1,
        decreases processed,
    {
        if processed <= 0 {
            k
        } else {
            let prev = Self::min_white_windows(s, k, processed - 1);
            let start = processed - 1;
            let here = Self::sum_range(s, start, start + k);
            if here < prev {
                here
            } else {
                prev
            }
        }
    }

    pub open spec fn valid_window_start(n: int, k: int, start: int) -> bool {
        0 <= start <= n - k
    }

    pub open spec fn whites_in_window(s: Seq<i64>, start: int, k: int) -> int
        recommends
            0 <= start,
            start + k <= s.len(),
    {
        Self::sum_range(s, start, start + k)
    }

    pub fn min_recolors(n: usize, k: usize, s: Vec<i64>) -> (result: usize)
        requires
            1 <= n,
            n <= 200000,
            1 <= k <= n,
            s.len() == n,
            forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
        ensures
            exists|start: int|
                Self::valid_window_start(n as int, k as int, start)
                    && result as int == Self::whites_in_window(s@, start, k as int),
            forall|start: int|
                Self::valid_window_start(n as int, k as int, start)
                    ==> result as int <= Self::whites_in_window(s@, start, k as int),
    {
        let mut cur: i64 = 0;
        let mut j: usize = 0;
        while j < k {
            cur = cur + s[j];
            j += 1;
        }

        let mut best: i64 = cur;
        let mut left: usize = 0;

        while left + k < n {
            let next = cur - s[left] + s[left + k];
            cur = next;
            left += 1;
            if cur < best {
                best = cur;
            }
        }

        best as usize
    }
}

}