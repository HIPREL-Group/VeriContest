use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn bad_prefix_count(s: Seq<i32>, hi: int, t: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0int
    } else {
        (if s[hi - 1] > t { 1int } else { 0int }) + bad_prefix_count(s, hi - 1, t)
    }
}

proof fn lemma_bad_prefix_count_step(s: Seq<i32>, hi: int, t: int)
    requires
        0 < hi <= s.len(),
    ensures
        bad_prefix_count(s, hi, t) == bad_prefix_count(s, hi - 1, t) + (if s[hi - 1] > t {
            1int
        } else {
            0int
        }),
{
}

proof fn lemma_bad_prefix_count_ge_zero(s: Seq<i32>, hi: int, t: int)
    requires
        0 <= hi <= s.len(),
    ensures
        bad_prefix_count(s, hi, t) >= 0,
    decreases hi,
{
    if hi == 0 {
    } else {
        lemma_bad_prefix_count_ge_zero(s, hi - 1, t);
        lemma_bad_prefix_count_step(s, hi, t);
        assert(bad_prefix_count(s, hi - 1, t) >= 0);
        assert(bad_prefix_count(s, hi, t) >= 0);
    }
}

proof fn lemma_bad_prefix_count_le_hi(s: Seq<i32>, hi: int, t: int)
    requires
        0 <= hi <= s.len(),
    ensures
        bad_prefix_count(s, hi, t) <= hi,
    decreases hi,
{
    if hi == 0 {
    } else {
        lemma_bad_prefix_count_le_hi(s, hi - 1, t);
        lemma_bad_prefix_count_step(s, hi, t);
        assert(bad_prefix_count(s, hi - 1, t) <= hi - 1);
        assert(bad_prefix_count(s, hi, t) <= hi);
    }
}

impl Solution {
    pub fn min_swaps_minimize_prefix_sum(p: Vec<i32>, n: usize, k: usize) -> (result: i32)
        requires
            p.len() == n,
            1 <= k <= n <= 100,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] && p[i] <= n as int,
        ensures
            (result as int) == bad_prefix_count(p@, k as int, k as int),
            0 <= (result as int) && (result as int) <= k as int,
    {
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < k
            invariant
                i <= k,
                p.len() == n,
                1 <= k <= n <= 100,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] p[j] && p[j] <= n as int,
                (cnt as int) == bad_prefix_count(p@, i as int, k as int),
                0 <= (cnt as int) && (cnt as int) <= i as int,
            decreases k - i,
        {
            proof {
                lemma_bad_prefix_count_step(p@, (i + 1) as int, k as int);
                assert(i < n);
                assert(p@[i as int] == p@.index(i as int));
            }
            if p[i] > k as i32 {
                cnt = cnt + 1;
            }
            i = i + 1;
            proof {
                assert((cnt as int) == bad_prefix_count(p@, i as int, k as int));
            }
        }
        proof {
            lemma_bad_prefix_count_le_hi(p@, k as int, k as int);
            lemma_bad_prefix_count_ge_zero(p@, k as int, k as int);
            assert((cnt as int) == bad_prefix_count(p@, k as int, k as int));
            assert(0 <= (cnt as int) && (cnt as int) <= k as int);
            assert forall|h: int|
                0 <= h && h <= k as int implies {
                    &&& 0 <= #[trigger] bad_prefix_count(p@, h, k as int)
                    &&& bad_prefix_count(p@, h, k as int) <= h
                } by {
                lemma_bad_prefix_count_le_hi(p@, h, k as int);
                lemma_bad_prefix_count_ge_zero(p@, h, k as int);
            }
        }
        cnt
    }
}

}
