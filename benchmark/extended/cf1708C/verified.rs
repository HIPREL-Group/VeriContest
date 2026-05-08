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

    pub fn optimal_tests(a: Vec<i64>, q: i64) -> (ans: Vec<u8>)
        requires
            1 <= a.len() <= 100_000,
            1 <= q <= 1_000_000_000,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        ensures
            ans@ == Self::solve(a@, q),
    {
        let n = a.len();
        let mut cur_q: i64 = 0;
        let mut ans: Vec<u8> = Vec::new();
        let mut fill: usize = 0;
        while fill < n
            invariant
                n == a.len(),
                0 <= fill <= n,
                ans.len() == fill,
                forall |k: int| 0 <= k < fill ==> ans@[k] == 0,
            decreases n - fill,
        {
            ans.push(0);
            fill = fill + 1;
        }

        let mut i: usize = n;
        while i > 0
            invariant
                1 <= n <= 100_000,
                n == a.len(),
                ans.len() == n,
                0 <= i <= n,
                0 <= cur_q <= q,
                Self::solve(a@, q) =~= Self::compute_ans(a@, q, i as int, cur_q as nat) + ans@.subrange(i as int, n as int),
            decreases i,
        {
            i = i - 1;
            let aval = a[i];

            if aval <= cur_q {
                ans[i] = 1;
                proof {
                    assert(Self::compute_ans(a@, q, (i + 1) as int, cur_q as nat) =~= Self::compute_ans(a@, q, i as int, cur_q as nat).push(1u8));
                }
            } else if cur_q < q {
                cur_q = cur_q + 1;
                ans[i] = 1;
                proof {
                    assert(Self::compute_ans(a@, q, (i + 1) as int, (cur_q - 1) as nat) =~= Self::compute_ans(a@, q, i as int, cur_q as nat).push(1u8));
                }
            } else {
                ans[i] = 0;
                proof {
                    assert(Self::compute_ans(a@, q, (i + 1) as int, cur_q as nat) =~= Self::compute_ans(a@, q, i as int, cur_q as nat).push(0u8));
                }
            }
        }
        
        proof {
            assert(ans@.subrange(0, n as int) =~= ans@);
            assert(Self::compute_ans(a@, q, 0, cur_q as nat) =~= Seq::empty());
        }
        
        ans
    }
}

}
