use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn circ_rest_segment(a: Seq<i32>, n: int, start: int, len: int) -> bool {
    &&& 0 <= start < n
    &&& 0 <= len
    &&& forall|k: int|
        0 <= k < len ==> #[trigger] a[(start + k) % n] == 1
}

pub open spec fn rest_run_len_ending_at(a: Seq<i32>, n: int, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= 2 * n {
        0
    } else if a[i % n] != 1 {
        0
    } else if i == 0 {
        1
    } else if a[(i - 1) % n] == 1 {
        rest_run_len_ending_at(a, n, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_rest_len_upto(a: Seq<i32>, n: int, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = rest_run_len_ending_at(a, n, hi);
        let prev = max_rest_len_upto(a, n, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn maximal_continuous_rest(a: Vec<i32>) -> (res: i32)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] == 0 || a[i] == 1,
            exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0,
        ensures
            0 <= (res as int) && (res as int) <= a.len() as int,
            (res as int) == max_rest_len_upto(a@, a.len() as int, 2 * (a.len() as int) - 1),
    {
        let n = a.len();
        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut i: usize = 0;
        let total: usize = 2 * n;
        while i < total {
            let idx: usize = i % n;
            if a[idx] == 1 {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

}
