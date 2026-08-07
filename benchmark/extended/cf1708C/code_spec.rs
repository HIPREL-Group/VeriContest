use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn compute_ans(a: Seq<i64>, q: i64, i: int, cur_q: nat) -> Seq<u8>
        recommends 0 <= i <= a.len(),
        decreases i,
    {
        if i <= 0 {
            Seq::empty()
        } else {
            let idx = i - 1;
            if a[idx] <= cur_q {
                Self::compute_ans(a, q, idx, cur_q).push(1u8)
            } else if cur_q < q {
                Self::compute_ans(a, q, idx, cur_q + 1nat).push(1u8)
            } else {
                Self::compute_ans(a, q, idx, cur_q).push(0u8)
            }
        }
    }

    pub open spec fn solve(a: Seq<i64>, q: i64) -> Seq<u8> {
        Self::compute_ans(a, q, a.len() as int, 0nat)
    }

    pub open spec fn is_bits(ans: Seq<u8>) -> bool {
        forall|k: int| 0 <= k < ans.len() ==> (#[trigger] ans[k] == 0 || ans[k] == 1)
    }

    pub open spec fn count_ones_range(ans: Seq<u8>, i: int, end: int) -> int
        decreases end - i,
    {
        if i >= end {
            0
        } else {
            (if ans[i] == 1 { 1int } else { 0int }) + Self::count_ones_range(ans, i + 1, end)
        }
    }

    pub open spec fn forward_run(a: Seq<i64>, ans: Seq<u8>, i: int, iq: int) -> int
        decreases a.len() - i,
    {
        if i >= a.len() {
            iq
        } else if iq < 0 {
            -1
        } else if ans[i] == 0 {
            Self::forward_run(a, ans, i + 1, iq)
        } else if iq <= 0 {
            -1
        } else if a[i] as int > iq {
            Self::forward_run(a, ans, i + 1, iq - 1)
        } else {
            Self::forward_run(a, ans, i + 1, iq)
        }
    }

    pub fn optimal_tests(a: Vec<i64>, q: i64) -> (ans: Vec<u8>)
        requires
            1 <= a.len() <= 100_000,
            1 <= q <= 1_000_000_000,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        ensures
            ans@.len() == a@.len(),
            Self::is_bits(ans@),
            Self::forward_run(a@, ans@, 0, q as int) >= 0,
            forall|other: Seq<u8>|
                other.len() == a@.len() && Self::is_bits(other) && Self::forward_run(a@, other, 0, q as int) >= 0
                    ==> #[trigger] Self::count_ones_range(other, 0, a@.len() as int)
                        <= Self::count_ones_range(ans@, 0, a@.len() as int),
    {
        let n = a.len();
        let mut cur_q: i64 = 0;
        let mut ans: Vec<u8> = Vec::new();
        let mut fill: usize = 0;
        while fill < n {
            ans.push(0);
            fill = fill + 1;
        }

        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let aval = a[i];

            if aval <= cur_q {
                ans[i] = 1;
            } else if cur_q < q {
                cur_q = cur_q + 1;
                ans[i] = 1;
            } else {
                ans[i] = 0;
            }
        }
        ans
    }
}

}
