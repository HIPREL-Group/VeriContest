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

    pub open spec fn block_sum(nums: Seq<i64>, lo: int, hi: int) -> int {
        Self::prefix_sum(nums, hi) - Self::prefix_sum(nums, lo)
    }

    pub open spec fn valid_equal_partition(
        a: Seq<i64>, na: int, b: Seq<i64>, nb: int,
        k: int, pa: Seq<int>, pb: Seq<int>,
    ) -> bool {
        &&& k >= 1
        &&& pa.len() == k + 1
        &&& pb.len() == k + 1
        &&& pa[0] == 0
        &&& pa[k] == na
        &&& pb[0] == 0
        &&& pb[k] == nb
        &&& forall|i: int| 0 <= i < k ==> pa[i] < #[trigger] pa[i + 1]
        &&& forall|i: int| 0 <= i < k ==> pb[i] < #[trigger] pb[i + 1]
        &&& forall|i: int| 0 <= i < k ==>
                Self::block_sum(a, pa[i], #[trigger] pa[i + 1])
                == Self::block_sum(b, pb[i], pb[i + 1])
    }

    pub fn max_equal_block_count(a: Vec<i64>, b: Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 300_000,
            1 <= b.len() <= 300_000,
            forall|x: int| 0 <= x < a.len() ==> 1 <= #[trigger] a[x] as int && (a[x] as int) <= 1_000_000_000,
            forall|x: int| 0 <= x < b.len() ==> 1 <= #[trigger] b[x] as int && (b[x] as int) <= 1_000_000_000,
            Self::total_sum(a@) <= i64::MAX,
            Self::total_sum(b@) <= i64::MAX,
        ensures
            (result == -1) == (Self::total_sum(a@) != Self::total_sum(b@)),
            result >= 0 ==> result >= 1,
            result >= 0 ==> exists|pa: Seq<int>, pb: Seq<int>|
                Self::valid_equal_partition(a@, a.len() as int, b@, b.len() as int, result as int, pa, pb),
    {
        proof {
            assert(Self::total_sum(a@) <= i64::MAX);
            assert(Self::total_sum(b@) <= i64::MAX);
        }
        let n = a.len();
        let m = b.len();
        let mut ta: i64 = 0;
        let mut tb: i64 = 0;
        let mut u = 0usize;
        while u < n
            invariant
                n == a.len(),
                u <= n,
                ta as int == Self::prefix_sum(a@, u as int),
                forall|x: int| 0 <= x < a.len() ==> 1 <= #[trigger] a[x] as int,
                Self::total_sum(a@) <= i64::MAX,
            decreases n - u,
        {
            proof {
                lemma_prefix_sum_step(a@, u as int);
                lemma_prefix_sum_le_total(a@, (u as int) + 1);
                lemma_prefix_sum_nonneg_at(a@, (u as int) + 1);
            }
            ta = ta + a[u];
            u = u + 1;
        }
        proof {
            assert(ta as int == Self::total_sum(a@));
        }
        u = 0usize;
        while u < m
            invariant
                m == b.len(),
                u <= m,
                tb as int == Self::prefix_sum(b@, u as int),
                forall|x: int| 0 <= x < b.len() ==> 1 <= #[trigger] b[x] as int,
                Self::total_sum(b@) <= i64::MAX,
            decreases m - u,
        {
            proof {
                lemma_prefix_sum_step(b@, u as int);
                lemma_prefix_sum_le_total(b@, (u as int) + 1);
                lemma_prefix_sum_nonneg_at(b@, (u as int) + 1);
            }
            tb = tb + b[u];
            u = u + 1;
        }
        proof {
            assert(tb as int == Self::total_sum(b@));
        }
        if ta != tb {
            proof {
                assert(Self::total_sum(a@) != Self::total_sum(b@));
            }
            return -1;
        }
        proof {
            assert(Self::total_sum(a@) == Self::total_sum(b@));
        }
        let mut i = 0usize;
        let mut j = 0usize;
        let mut sa: i64 = 0;
        let mut sb: i64 = 0;
        let mut ans: i64 = 0;
        proof {
            reveal_with_fuel(Solution::prefix_sum, 2);
            assert(Self::prefix_sum(a@, 0) == 0);
            assert(Self::prefix_sum(b@, 0) == 0);
        }
        let ghost mut seg_i: int = 0;
        let ghost mut seg_j: int = 0;
        let ghost mut gpa: Seq<int> = Seq::empty().push(0int);
        let ghost mut gpb: Seq<int> = Seq::empty().push(0int);
        while i < n || j < m
            invariant
                n == a.len(),
                m == b.len(),
                n <= 300_000,
                m <= 300_000,
                i <= n,
                j <= m,
                0 <= seg_i && seg_i <= i as int,
                0 <= seg_j && seg_j <= j as int,
                forall|x: int| 0 <= x < a.len() ==> 1 <= #[trigger] a[x] as int,
                forall|x: int| 0 <= x < b.len() ==> 1 <= #[trigger] b[x] as int,
                Self::total_sum(a@) == Self::total_sum(b@),
                Self::total_sum(a@) <= i64::MAX,
                Self::total_sum(b@) <= i64::MAX,
                sa as int == Self::prefix_sum(a@, i as int) - Self::prefix_sum(a@, seg_i),
                sb as int == Self::prefix_sum(b@, j as int) - Self::prefix_sum(b@, seg_j),
                0 <= sa as int && 0 <= sb as int,
                0 <= ans,
                seg_i as int >= ans as int,
                seg_j as int >= ans as int,
                Self::prefix_sum(a@, seg_i) == Self::prefix_sum(b@, seg_j),
                sa as int == sb as int ==> sa == 0i64,
                gpa.len() == (ans as int) + 1,
                gpb.len() == (ans as int) + 1,
                gpa[0] == 0int,
                gpb[0] == 0int,
                gpa[ans as int] == seg_i,
                gpb[ans as int] == seg_j,
                forall|p: int| 0 <= p < ans as int ==> gpa[p] < #[trigger] gpa[p + 1],
                forall|p: int| 0 <= p < ans as int ==> gpb[p] < #[trigger] gpb[p + 1],
                forall|p: int| 0 <= p <= ans as int ==>
                    Self::prefix_sum(a@, #[trigger] gpa[p]) == Self::prefix_sum(b@, gpb[p]),
            decreases (n + m) - (i + j),
        {
            proof {
                assert((i as int) < (n as int) || (j as int) < (m as int));
                assert((i as int) + (j as int) < (n as int) + (m as int));
            }
            if sa <= sb {
                if i < n {
                    proof {
                        let ii: int = i as int;
                        lemma_prefix_sum_mono(a@, seg_i, ii);
                        lemma_prefix_sum_step(a@, ii);
                        let t1: int = Self::prefix_sum(a@, ii + 1) - Self::prefix_sum(a@, seg_i);
                        assert((sa as int) + (a@[ii] as int) == t1);
                        lemma_prefix_sum_le_total(a@, ii + 1);
                        lemma_prefix_sum_nonneg_at(a@, seg_i);
                        lemma_prefix_sum_mono(a@, ii + 1, a.len() as int);
                        assert(t1 <= Self::total_sum(a@));
                        assert((sa as int) + (a@[ii] as int) <= i64::MAX);
                    }
                    sa = sa + a[i];
                    i = i + 1;
                } else {
                    proof {
                        let jj: int = j as int;
                        lemma_prefix_sum_mono(b@, seg_j, jj);
                        lemma_prefix_sum_step(b@, jj);
                        let t2: int = Self::prefix_sum(b@, jj + 1) - Self::prefix_sum(b@, seg_j);
                        assert((sb as int) + (b@[jj] as int) == t2);
                        lemma_prefix_sum_le_total(b@, jj + 1);
                        lemma_prefix_sum_nonneg_at(b@, seg_j);
                        lemma_prefix_sum_mono(b@, jj + 1, b.len() as int);
                        assert((sb as int) + (b@[jj] as int) <= i64::MAX);
                    }
                    sb = sb + b[j];
                    j = j + 1;
                }
            } else {
                if j < m {
                    proof {
                        let jj2: int = j as int;
                        lemma_prefix_sum_mono(b@, seg_j, jj2);
                        lemma_prefix_sum_step(b@, jj2);
                        let t3: int = Self::prefix_sum(b@, jj2 + 1) - Self::prefix_sum(b@, seg_j);
                        assert((sb as int) + (b@[jj2] as int) == t3);
                        lemma_prefix_sum_le_total(b@, jj2 + 1);
                        lemma_prefix_sum_nonneg_at(b@, seg_j);
                        lemma_prefix_sum_mono(b@, jj2 + 1, b.len() as int);
                        assert((sb as int) + (b@[jj2] as int) <= i64::MAX);
                    }
                    sb = sb + b[j];
                    j = j + 1;
                } else {
                    proof {
                        let ii2: int = i as int;
                        lemma_prefix_sum_mono(a@, seg_i, ii2);
                        lemma_prefix_sum_step(a@, ii2);
                        let t4: int = Self::prefix_sum(a@, ii2 + 1) - Self::prefix_sum(a@, seg_i);
                        assert((sa as int) + (a@[ii2] as int) == t4);
                        lemma_prefix_sum_le_total(a@, ii2 + 1);
                        lemma_prefix_sum_nonneg_at(a@, seg_i);
                        lemma_prefix_sum_mono(a@, ii2 + 1, a.len() as int);
                        assert((sa as int) + (a@[ii2] as int) <= i64::MAX);
                    }
                    sa = sa + a[i];
                    i = i + 1;
                }
            }
            if sa == sb && sa > 0 {
                proof {
                    assert(Self::prefix_sum(a@, i as int) == Self::prefix_sum(b@, j as int));
                    lemma_positive_tail_implies_hi_gt_lo(a@, seg_i, i as int);
                    lemma_positive_tail_implies_hi_gt_lo(b@, seg_j, j as int);
                    assert((i as int) > seg_i);
                    assert((j as int) > seg_j);
                    assert((ans as int) + 1 <= (i as int));
                    assert((ans as int) + 1 <= (j as int));
                    assert((i as int) <= (n as int));
                    assert((ans as int) + 1 <= (n as int));
                    assert((n as int) <= 300_000);
                    assert((ans as int) + 1 <= i64::MAX);
                    let old_ans = ans as int;
                    gpa = gpa.push(i as int);
                    gpb = gpb.push(j as int);
                    assert(gpa.len() == old_ans + 2);
                    assert(gpb.len() == old_ans + 2);
                    assert(gpa[old_ans + 1] == i as int);
                    assert(gpb[old_ans + 1] == j as int);
                }
                ans = ans + 1;
                sa = 0;
                sb = 0;
                proof {
                    seg_i = i as int;
                    seg_j = j as int;
                }
            }
        }
        proof {
            assert(i == n);
            assert(j == m);
            assert(sa as int == Self::prefix_sum(a@, n as int) - Self::prefix_sum(a@, seg_i));
            assert(sb as int == Self::prefix_sum(b@, m as int) - Self::prefix_sum(b@, seg_j));
            assert(Self::prefix_sum(a@, seg_i) == Self::prefix_sum(b@, seg_j));
            assert(Self::total_sum(a@) == Self::total_sum(b@));
            assert(sa as int == sb as int);
            assert(sa == 0i64);
            lemma_equal_prefix_sum_implies_equal_idx(a@, seg_i, n as int);
            assert(seg_i == n as int);
            lemma_equal_prefix_sum_implies_equal_idx(b@, seg_j, m as int);
            assert(seg_j == m as int);
            assert(gpa[ans as int] == n as int);
            assert(gpb[ans as int] == m as int);
            if ans == 0 {
                assert(gpa[0] == 0int);
                assert(gpa[0] == n as int);
                assert(n == 0);
                assert(false);
            }
            assert(ans >= 1);
            assert forall|p: int| 0 <= p < ans as int implies
                Self::block_sum(a@, gpa[p], #[trigger] gpa[p + 1])
                == Self::block_sum(b@, gpb[p], gpb[p + 1])
            by {
                assert(Self::prefix_sum(a@, gpa[p]) == Self::prefix_sum(b@, gpb[p]));
                assert(Self::prefix_sum(a@, gpa[p + 1]) == Self::prefix_sum(b@, gpb[p + 1]));
            }
            assert(Self::valid_equal_partition(
                a@, n as int, b@, m as int, ans as int, gpa, gpb,
            ));
            assert(!(Self::total_sum(a@) != Self::total_sum(b@)));
        }
        ans
    }
}

proof fn lemma_prefix_sum_step(nums: Seq<i64>, i: int)
    requires
        0 <= i < nums.len(),
    ensures
        Solution::prefix_sum(nums, i + 1) == Solution::prefix_sum(nums, i) + nums[i] as int,
{
}

proof fn lemma_prefix_sum_le_total(nums: Seq<i64>, i: int)
    requires
        0 <= i <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, i) <= Solution::total_sum(nums),
    decreases nums.len() - i,
{
    if i == nums.len() as int {
    } else {
        lemma_prefix_sum_step(nums, i);
        lemma_prefix_sum_le_total(nums, i + 1);
    }
}

proof fn lemma_prefix_sum_nonneg_at(nums: Seq<i64>, end: int)
    requires
        0 <= end <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, end) >= 0,
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_prefix_sum_nonneg_at(nums, end - 1);
    }
}

proof fn lemma_prefix_sum_mono(nums: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, a) <= Solution::prefix_sum(nums, b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_prefix_sum_mono(nums, a, b - 1);
    }
}

proof fn lemma_positive_tail_implies_hi_gt_lo(nums: Seq<i64>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
        Solution::prefix_sum(nums, hi) - Solution::prefix_sum(nums, lo) > 0,
    ensures
        lo < hi,
{
    if lo >= hi {
        assert(lo == hi);
        assert(Solution::prefix_sum(nums, hi) - Solution::prefix_sum(nums, lo) == 0);
        assert(false);
    }
}

proof fn lemma_equal_prefix_sum_implies_equal_idx(nums: Seq<i64>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
        Solution::prefix_sum(nums, lo) == Solution::prefix_sum(nums, hi),
    ensures
        lo == hi,
{
    if lo < hi {
        lemma_prefix_sum_step(nums, lo);
        lemma_prefix_sum_mono(nums, lo + 1, hi);
    }
}

}
