use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn total_sum(nums: Seq<i64>) -> int {
        Self::prefix_sum(nums, nums.len() as int)
    }

    pub open spec fn block_sum(nums: Seq<i64>, lo: int, hi: int) -> int
        recommends
            0 <= lo <= hi <= nums.len(),
    {
        Self::prefix_sum(nums, hi) - Self::prefix_sum(nums, lo)
    }

    pub open spec fn petya_wins(a: Seq<i64>, n: int, s: int, k: int) -> bool {
        &&& a.len() == n
        &&& Self::total_sum(a) == s
        &&& forall|i: int| 0 <= i < n ==> #[trigger] a[i] as int >= 1
        &&& 0 <= k <= s
        &&& forall|lo: int, hi: int|
            0 <= lo < hi <= n ==> #[trigger] Self::block_sum(a, lo, hi) != k
                && Self::block_sum(a, lo, hi) != s - k
    }

    proof fn lemma_prefix_ones_is_end(a: Seq<i64>, end: int)
        requires
            0 <= end <= a.len(),
            forall|j: int| 0 <= j < end ==> #[trigger] a[j] as int == 1,
        ensures
            Self::prefix_sum(a, end) == end,
        decreases end,
    {
        if end <= 0 {
        } else {
            Self::lemma_prefix_ones_is_end(a, (end - 1) as int);
            assert(a[end - 1] as int == 1);
            assert(Self::prefix_sum(a, end) == Self::prefix_sum(a, end - 1) + 1);
        }
    }

    proof fn lemma_total_of_constructed(nn: int, ss: int, a: Seq<i64>)
        requires
            nn >= 1,
            ss >= 2 * nn,
            a.len() == nn,
            forall|i: int| 0 <= i < nn - 1 ==> #[trigger] a[i] as int == 1,
            a[nn - 1] as int == ss - nn + 1,
        ensures
            Self::total_sum(a) == ss,
    {
        Self::lemma_prefix_ones_is_end(a, nn - 1);
        assert(Self::prefix_sum(a, nn) == Self::prefix_sum(a, nn - 1) + a[nn - 1] as int);
        assert(Self::prefix_sum(a, nn - 1) == nn - 1);
        assert(a[nn - 1] as int == ss - nn + 1);
        assert(Self::prefix_sum(a, nn) == (nn - 1) + (ss - nn + 1));
        assert((nn - 1) + (ss - nn + 1) == ss);
    }

    proof fn lemma_block_ones_run(a: Seq<i64>, lo: int, hi: int)
        requires
            0 <= lo <= hi,
            hi <= a.len(),
            forall|j: int| lo <= j < hi ==> #[trigger] a[j] as int == 1,
        ensures
            Self::block_sum(a, lo, hi) == hi - lo,
        decreases hi - lo,
    {
        if lo == hi {
            assert(Self::block_sum(a, lo, hi) == 0);
        } else {
            assert(lo < hi);
            assert(a[lo] as int == 1);
            assert(Self::prefix_sum(a, lo + 1) == Self::prefix_sum(a, lo) + 1) by {
                assert(Self::prefix_sum(a, lo + 1) == Self::prefix_sum(a, lo) + a[lo] as int);
            };
            Self::lemma_block_ones_run(a, lo + 1, hi);
            assert(Self::block_sum(a, lo, hi) == Self::prefix_sum(a, hi) - Self::prefix_sum(a, lo));
            assert(Self::block_sum(a, lo + 1, hi) == hi - (lo + 1));
            assert(Self::prefix_sum(a, hi) - Self::prefix_sum(a, lo)
                == (Self::prefix_sum(a, hi) - Self::prefix_sum(a, lo + 1))
                    + (Self::prefix_sum(a, lo + 1) - Self::prefix_sum(a, lo)));
            assert(Self::prefix_sum(a, hi) - Self::prefix_sum(a, lo + 1) == Self::block_sum(a, lo + 1, hi));
            assert(Self::block_sum(a, lo, hi) == 1 + (hi - lo - 1));
            assert(1 + (hi - lo - 1) == hi - lo);
        }
    }

    proof fn lemma_block_hi_le_n_minus_one(
        a: Seq<i64>,
        nn: int,
        ss: int,
        lo: int,
        hi: int,
    )
        requires
            a.len() == nn,
            0 <= lo < hi <= nn,
            hi <= nn - 1,
            nn >= 2,
            ss >= 2 * nn,
            forall|i: int| 0 <= i < nn - 1 ==> #[trigger] a[i] as int == 1,
            a[nn - 1] as int == ss - nn + 1,
        ensures
            Self::block_sum(a, lo, hi) != nn,
            Self::block_sum(a, lo, hi) != ss - nn,
    {
        assert(forall|j: int| lo <= j < hi ==> a[j] as int == 1) by {
            assert forall|j: int| lo <= j < hi implies a[j] as int == 1 by {
                assert(0 <= j && j < nn - 1);
            };
        };
        Self::lemma_block_ones_run(a, lo, hi);
        assert(Self::block_sum(a, lo, hi) == hi - lo);
        assert(hi - lo <= nn - 1);
        assert(hi - lo < nn);
        assert(Self::block_sum(a, lo, hi) != nn);
        assert(ss - nn >= nn);
        assert(hi - lo < ss - nn);
        assert(Self::block_sum(a, lo, hi) != ss - nn);
    }

    proof fn lemma_block_hi_eq_nn_lo_eq_nn_minus_one(
        a: Seq<i64>,
        nn: int,
        ss: int,
    )
        requires
            a.len() == nn,
            nn >= 1,
            ss >= 2 * nn,
            forall|i: int| 0 <= i < nn - 1 ==> #[trigger] a[i] as int == 1,
            a[nn - 1] as int == ss - nn + 1,
        ensures
            Self::block_sum(a, nn - 1, nn) != nn,
            Self::block_sum(a, nn - 1, nn) != ss - nn,
    {
        assert(Self::block_sum(a, nn - 1, nn) == a[nn - 1] as int);
        assert(a[nn - 1] as int == ss - nn + 1);
        assert(ss - nn + 1 != ss - nn);
        assert(Self::block_sum(a, nn - 1, nn) != ss - nn);
        assert(ss - nn + 1 != nn) by {
            if ss - nn + 1 == nn {
                assert(ss + 1 == 2 * nn);
                assert(ss == 2 * nn - 1);
                assert(ss < 2 * nn);
                assert(false);
            }
        };
        assert(Self::block_sum(a, nn - 1, nn) != nn);
    }

    proof fn lemma_block_hi_eq_nn_lo_lt_nn_minus_one(
        a: Seq<i64>,
        nn: int,
        ss: int,
        lo: int,
    )
        requires
            a.len() == nn,
            nn >= 2,
            0 <= lo <= nn - 2,
            ss >= 2 * nn,
            forall|i: int| 0 <= i < nn - 1 ==> #[trigger] a[i] as int == 1,
            a[nn - 1] as int == ss - nn + 1,
        ensures
            Self::block_sum(a, lo, nn) != nn,
            Self::block_sum(a, lo, nn) != ss - nn,
    {
        Self::lemma_prefix_ones_is_end(a, lo);
        assert(Self::prefix_sum(a, lo) == lo);
        Self::lemma_total_of_constructed(nn, ss, a);
        assert(Self::prefix_sum(a, nn) == ss);
        assert(Self::block_sum(a, lo, nn) == Self::prefix_sum(a, nn) - Self::prefix_sum(a, lo));
        assert(Self::block_sum(a, lo, nn) == ss - lo);
        assert(lo <= nn - 2);
        assert(ss - lo >= ss - (nn - 2));
        assert(ss - nn + 1 >= nn + 1) by {
            assert(ss >= 2 * nn);
            assert(ss - nn + 1 - (nn + 1) == ss - 2 * nn);
            assert(ss - 2 * nn >= 0);
        };
        assert(ss - lo >= nn + 2);
        assert(Self::block_sum(a, lo, nn) > nn);
        assert(Self::block_sum(a, lo, nn) != nn);
        assert((ss - lo) != (ss - nn)) by {
            assert(lo != nn);
        };
        assert(Self::block_sum(a, lo, nn) != ss - nn);
    }

    proof fn lemma_petya_wins_constructed(nn: int, ss: int, a: Seq<i64>)
        requires
            nn >= 1,
            ss >= 2 * nn,
            a.len() == nn,
            forall|i: int| 0 <= i < nn - 1 ==> #[trigger] a[i] as int == 1,
            a[nn - 1] as int == ss - nn + 1,
        ensures
            Self::petya_wins(a, nn, ss, nn),
    {
        Self::lemma_total_of_constructed(nn, ss, a);
        assert(0 <= nn && nn <= ss);
        assert forall|lo: int, hi: int|
            0 <= lo && lo < hi && hi <= nn implies ({
                &&& Self::block_sum(a, lo, hi) != nn
                &&& Self::block_sum(a, lo, hi) != ss - nn
            }) by {
            assert(0 <= lo < hi <= nn);
            if hi <= nn - 1 {
                assert(nn >= 2);
                Self::lemma_block_hi_le_n_minus_one(a, nn, ss, lo, hi);
            } else {
                assert(hi == nn);
                if lo == nn - 1 {
                    Self::lemma_block_hi_eq_nn_lo_eq_nn_minus_one(a, nn, ss);
                } else {
                    assert(lo < nn - 1);
                    assert(0 <= lo <= nn - 2);
                    Self::lemma_block_hi_eq_nn_lo_lt_nn_minus_one(a, nn, ss, lo);
                }
            }
        };
        assert(Self::petya_wins(a, nn, ss, nn));
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn construct_game(n: i64, s: i64) -> (result: Option<(Vec<i64>, i64)>)
        requires
            1 <= n <= s <= 1_000_000,
        ensures
            result == None::<(Vec<i64>, i64)> <==> (s as int) < 2 * (n as int),
            result != None::<(Vec<i64>, i64)> ==> {
                let p = result->Some_0;
                &&& p.0.len() == n as usize
                &&& p.1 == n
                &&& Self::petya_wins(p.0@, n as int, s as int, p.1 as int)
            },
    {
        if s < 2 * n {
            proof {
                assert((s as int) < 2 * (n as int));
            }
            return None;
        }
        proof {
            assert((s as int) >= 2 * (n as int));
        }
        let nu = n as usize;
        let mut a: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < nu - 1
            invariant
                nu == n as usize,
                1 <= n <= 1_000_000,
                i <= nu - 1,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == 1,
            decreases nu - 1 - i,
        {
            a.push(1i64);
            i = i + 1;
        }
        proof {
            assert(i == nu - 1);
            assert(a.len() == nu - 1);
            assert(forall|j: int| 0 <= j < (nu - 1) as int ==> a@[j] == 1);
        }
        a.push(s - (n - 1));
        proof {
            let nn = n as int;
            let ss = s as int;
            assert(a@.len() == nn);
            assert(forall|j: int| 0 <= j < nn - 1 ==> #[trigger] a@[j] == 1);
            assert(a@[nn - 1] == s - (n - 1));
            assert(a@[nn - 1] as int == ss - nn + 1);
            Self::lemma_petya_wins_constructed(nn, ss, a@);
            assert(Self::petya_wins(a@, nn, ss, n as int));
        }
        Some((a, n))
    }
}

}
