use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn common_at(a: Seq<i32>, b: Seq<i32>, i: int, j: int, L: int) -> bool {
        0 <= i && i + L <= a.len()
        && 0 <= j && j + L <= b.len()
        && forall |k: int| 0 <= k < L ==> (#[trigger] a[i + k]) == b[j + k]
    }

    pub open spec fn lcs_suffix(a: Seq<i32>, b: Seq<i32>, i: int, j: int) -> int
        decreases i + j,
    {
        if i <= 0 || j <= 0 {
            0
        } else if a[i - 1] == b[j - 1] {
            1 + Self::lcs_suffix(a, b, i - 1, j - 1)
        } else {
            0
        }
    }

    proof fn lemma_lcs_suffix_common_at(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
        requires
            0 <= i <= a.len(),
            0 <= j <= b.len(),
        ensures
            Self::common_at(a, b, i - Self::lcs_suffix(a, b, i, j), j - Self::lcs_suffix(a, b, i, j),
                Self::lcs_suffix(a, b, i, j)),
        decreases i + j,
    {
        if i > 0 && j > 0 && a[i - 1] == b[j - 1] {
            Self::lemma_lcs_suffix_common_at(a, b, i - 1, j - 1);
        }
    }

    proof fn lemma_lcs_suffix_bound(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
        requires 0 <= i <= a.len(), 0 <= j <= b.len(),
        ensures Self::lcs_suffix(a, b, i, j) <= i, Self::lcs_suffix(a, b, i, j) <= j,
        decreases i + j,
    {
        if i > 0 && j > 0 && a[i - 1] == b[j - 1] {
            Self::lemma_lcs_suffix_bound(a, b, i - 1, j - 1);
        }
    }

    proof fn lemma_lcs_suffix_zero(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
        requires 0 <= i <= a.len(), 0 <= j <= b.len(), i == 0 || j == 0,
        ensures Self::lcs_suffix(a, b, i, j) == 0,
    {
        reveal_with_fuel(Solution::lcs_suffix, 2);
    }

    proof fn lemma_common_at_implies_lcs(a: Seq<i32>, b: Seq<i32>, i: int, j: int, L: int)
        requires
            0 <= L,
            0 <= i && i + L <= a.len(),
            0 <= j && j + L <= b.len(),
            Self::common_at(a, b, i, j, L),
        ensures
            Self::lcs_suffix(a, b, i + L, j + L) >= L,
        decreases L,
    {
        if L <= 0 {
            Self::lemma_lcs_suffix_nonneg(a, b, i + L, j + L);
            assert(Self::lcs_suffix(a, b, i + L, j + L) >= L);
        } else if L > 0 {
            assert(forall |k: int| 0 <= k < L ==> (#[trigger] a[i + k]) == b[j + k]);
            assert(0 <= 0 < L);
            assert((#[trigger] a[i + 0]) == b[j + 0]);
            assert(a[i] == b[j]);
            assert forall |k: int| 0 <= k < L - 1 implies (#[trigger] a[i + 1 + k]) == b[j + 1 + k] by {
                if 0 <= k < L - 1 {
                    assert(0 <= k + 1 < L);
                    assert((#[trigger] a[i + (k + 1)]) == b[j + (k + 1)]);
                }
            };
            assert(0 <= i + 1 && (i + 1) + (L - 1) <= a.len());
            assert(0 <= j + 1 && (j + 1) + (L - 1) <= b.len());
            assert(Self::common_at(a, b, i + 1, j + 1, L - 1));
            Self::lemma_common_at_implies_lcs(a, b, i + 1, j + 1, L - 1);
            assert(Self::lcs_suffix(a, b, i + L, j + L) >= L - 1);
            assert forall |k: int| 0 <= k < L - 1 implies (#[trigger] a[i + k]) == b[j + k] by {
                if 0 <= k < L - 1 {
                    assert(0 <= k < L);
                    assert((#[trigger] a[i + k]) == b[j + k]);
                }
            };
            assert(0 <= i && i + (L - 1) <= a.len());
            assert(0 <= j && j + (L - 1) <= b.len());
            assert(Self::common_at(a, b, i, j, L - 1));
            Self::lemma_common_at_implies_lcs(a, b, i, j, L - 1);
            assert(Self::lcs_suffix(a, b, i + (L - 1), j + (L - 1)) >= L - 1);
            assert(0 <= L - 1);
            assert(a[i + L - 1] == b[j + L - 1]);
            reveal_with_fuel(Solution::lcs_suffix, 3);
            assert(Self::lcs_suffix(a, b, i + L, j + L)
                == 1 + Self::lcs_suffix(a, b, i + L - 1, j + L - 1));
            assert(Self::lcs_suffix(a, b, i + L, j + L) >= L);
        }
    }

    proof fn lemma_lcs_suffix_nonneg(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
        requires 0 <= i <= a.len(), 0 <= j <= b.len(),
        ensures Self::lcs_suffix(a, b, i, j) >= 0,
        decreases i + j,
    {
        if i > 0 && j > 0 {
            Self::lemma_lcs_suffix_nonneg(a, b, i - 1, j - 1);
        }
    }

    proof fn lemma_max_no_longer(a: Seq<i32>, b: Seq<i32>, M: int, i: int, j: int, L: int)
        requires
            0 <= i <= a.len(),
            0 <= j <= b.len(),
            M >= 0,
            forall |ii: int, jj: int|
                0 <= ii <= a.len() && 0 <= jj <= b.len()
                    ==> Self::lcs_suffix(a, b, ii, jj) <= M,
            L > M,
            Self::common_at(a, b, i, j, L),
        ensures false,
    {
        Self::lemma_common_at_implies_lcs(a, b, i, j, L);
    }

    proof fn lemma_idx_col0_disjoint(gi: int, gj: int, gn: int, ii: int)
        requires
            gj >= 1,
            gn >= 1,
            gj <= gn,
            0 <= ii,
            0 <= gi,
        ensures
            gi * (gn + 1) + gj != ii * (gn + 1),
    {
        if ii == gi {
            assert(gi * (gn + 1) + gj != ii * (gn + 1));
        } else if ii > gi {
            assert(ii * (gn + 1) >= (gi + 1) * (gn + 1))
                by(nonlinear_arith) requires ii > gi, gn >= 0;
            assert((gi + 1) * (gn + 1) == gi * (gn + 1) + gn + 1)
                by(nonlinear_arith);
            assert(gi * (gn + 1) + gj < gi * (gn + 1) + gn + 1);
        } else {
            assert(ii * (gn + 1) <= (gi - 1) * (gn + 1))
                by(nonlinear_arith) requires ii < gi, gn >= 0;
            assert(gi * (gn + 1) + gj > gi * (gn + 1));
            assert(gi * (gn + 1) > (gi - 1) * (gn + 1))
                by(nonlinear_arith) requires gi >= 1, gn >= 0;
        }
    }

    proof fn lemma_flat_idx_injective(gn: int, i1: int, j1: int, i2: int, j2: int)
        requires
            gn >= 0,
            0 <= j1 <= gn,
            0 <= j2 <= gn,
            0 <= i1, 0 <= i2,
            i1 * (gn + 1) + j1 == i2 * (gn + 1) + j2,
        ensures
            i1 == i2, j1 == j2,
    {
        if i1 > i2 {
            assert((i1 - i2) * (gn + 1) == j2 - j1)
                by(nonlinear_arith)
                requires i1 * (gn + 1) + j1 == i2 * (gn + 1) + j2;
            assert((i1 - i2) * (gn + 1) >= gn + 1)
                by(nonlinear_arith)
                requires i1 > i2, gn >= 0;
        } else if i1 < i2 {
            assert((i2 - i1) * (gn + 1) == j1 - j2)
                by(nonlinear_arith)
                requires i1 * (gn + 1) + j1 == i2 * (gn + 1) + j2;
            assert((i2 - i1) * (gn + 1) >= gn + 1)
                by(nonlinear_arith)
                requires i2 > i1, gn >= 0;
        }
    }

    #[verifier::loop_isolation(false)]
    pub fn find_length(nums1: Vec<i32>, nums2: Vec<i32>) -> (res: i32)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            (nums1.len() + 1) * (nums2.len() + 1) <= usize::MAX,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 100,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 100,
        ensures
            res >= 0,
            res <= (nums1.len() as int) && res <= (nums2.len() as int),
            exists |i: int, j: int| Self::common_at(nums1@, nums2@, i, j, res as int),
            forall |L: int, i: int, j: int|
                (L > res as int && (#[trigger] Self::common_at(nums1@, nums2@, i, j, L))) ==> false,
    {
        broadcast use vstd::std_specs::vec::axiom_spec_len;

        let m = nums1.len();
        let n = nums2.len();
        let total = (m + 1) * (n + 1);
        let ghost gm = m as int;
        let ghost gn = n as int;
        let ghost gt = total as int;

        let mut dp: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        let ghost mut max_ii = 0int;
        let ghost mut max_jj = 0int;
        while idx < total
            invariant
                idx <= total,
                dp.len() == idx,
                forall |k: int| 0 <= k < idx as int ==> dp@[k] == 0,
            decreases total - idx
        {
            dp.push(0);
            idx += 1;
        }

        proof {
            assert(gt == (gm + 1) * (gn + 1));
        }

        let mut max_len = 0i32;
        let mut i = 1usize;

        while i <= m
            invariant
                m == nums1.len(),
                n == nums2.len(),
                gm == m as int,
                gn == n as int,
                gt == total as int,
                gt == (gm + 1) * (gn + 1),
                1 <= gm <= 1000,
                1 <= gn <= 1000,
                1 <= i <= m + 1,
                dp.len() == total,
                forall |ii: int, jj: int|
                    0 <= ii < i as int && 0 <= jj <= gn
                    && 0 <= ii * (gn + 1) + jj < gt ==>
                    dp@[ii * (gn + 1) + jj]
                        == Self::lcs_suffix(nums1@, nums2@, ii, jj),
                forall |k: int| 0 <= k < gt ==> 0 <= dp@[k],
                forall |ii: int| #![trigger dp@[ii * (gn + 1)]]
                    0 <= ii <= gm
                    && 0 <= ii * (gn + 1) < gt ==>
                    dp@[ii * (gn + 1)] == 0,
                max_len >= 0,
                max_len as int <= gm,
                max_len as int <= gn,
                forall |ii: int, jj: int|
                    0 <= ii < i as int && 0 <= jj <= gn
                    && 0 <= ii * (gn + 1) + jj < gt ==>
                    (#[trigger] dp@[ii * (gn + 1) + jj]) <= max_len as int,
                0 <= max_ii <= gm,
                0 <= max_jj <= gn,
                max_len as int == 0
                    || (0 <= max_ii * (gn + 1) + max_jj < gt
                        && dp@[max_ii * (gn + 1) + max_jj] == max_len as int),
                max_len as int > 0 ==> (0 <= max_ii < i as int && 0 <= max_jj <= gn),
            decreases m + 1 - i
        {
            proof {
                if i == 1 {
                    assert forall |ii: int, jj: int|
                        ii == 0 && 0 <= jj <= gn
                        && 0 <= ii * (gn + 1) + jj < gt
                        implies dp@[ii * (gn + 1) + jj]
                            == Self::lcs_suffix(nums1@, nums2@, ii, jj)
                    by {
                        Self::lemma_lcs_suffix_zero(nums1@, nums2@, 0, jj);
                    };
                }
                Self::lemma_lcs_suffix_zero(nums1@, nums2@, i as int, 0);
                assert(0 <= i as int * (gn + 1) < gt)
                    by(nonlinear_arith)
                    requires 1 <= i as int <= gm, gt == (gm + 1) * (gn + 1), gn >= 1;
                assert(dp@[i as int * (gn + 1)] == 0);
            }

            let mut j = 1usize;
            while j <= n
                invariant
                    1 <= j <= n + 1,
                    i <= m,
                    dp.len() == total,
                    forall |ii: int, jj: int|
                        ((0 <= ii < i as int && 0 <= jj <= gn)
                            || (ii == i as int && 0 <= jj < j as int))
                        && 0 <= ii * (gn + 1) + jj < gt ==>
                        dp@[ii * (gn + 1) + jj]
                            == Self::lcs_suffix(nums1@, nums2@, ii, jj),
                    forall |k: int| 0 <= k < gt ==> 0 <= dp@[k],
                    forall |ii: int| #![trigger dp@[ii * (gn + 1)]]
                        0 <= ii <= gm
                        && 0 <= ii * (gn + 1) < gt ==>
                        dp@[ii * (gn + 1)] == 0,
                    max_len >= 0,
                    max_len as int <= gm,
                    max_len as int <= gn,
                    forall |ii: int, jj: int|
                        ((0 <= ii < i as int && 0 <= jj <= gn)
                            || (ii == i as int && 0 <= jj < j as int))
                        && 0 <= ii * (gn + 1) + jj < gt ==>
                        (#[trigger] dp@[ii * (gn + 1) + jj]) <= max_len as int,
                    0 <= max_ii <= gm,
                    0 <= max_jj <= gn,
                    max_len as int == 0
                        || (0 <= max_ii * (gn + 1) + max_jj < gt
                            && dp@[max_ii * (gn + 1) + max_jj] == max_len as int),
                    max_len as int > 0 ==> (
                        (0 <= max_ii < i as int && 0 <= max_jj <= gn)
                        || (max_ii == i as int && 0 <= max_jj < j as int)
                    ),
                decreases n + 1 - j
            {
                let gi: Ghost<int> = Ghost(i as int);
                let gj: Ghost<int> = Ghost(j as int);
                proof {
                    assert(gi@ * (gn + 1) + gj@ < gt)
                        by(nonlinear_arith)
                        requires gi@ <= gm, gj@ <= gn,
                            gt == (gm + 1) * (gn + 1), gn >= 1, gm >= 1;
                    assert((gi@ - 1) * (gn + 1) + (gj@ - 1) >= 0)
                        by(nonlinear_arith)
                        requires gi@ >= 1, gj@ >= 1, gn >= 0;
                    assert((gi@ - 1) * (gn + 1) + (gj@ - 1) < gt)
                        by(nonlinear_arith)
                        requires gi@ <= gm, gj@ <= gn,
                            gt == (gm + 1) * (gn + 1), gi@ >= 1, gj@ >= 1,
                            gn >= 1, gm >= 1;
                }

                let cur_idx = i * (n + 1) + j;
                let prev_idx = (i - 1) * (n + 1) + (j - 1);

                proof {
                    assert(cur_idx as int == gi@ * (gn + 1) + gj@);
                    assert(prev_idx as int == (gi@ - 1) * (gn + 1) + (gj@ - 1));
                    assert(dp@[prev_idx as int]
                        == Self::lcs_suffix(nums1@, nums2@, gi@ - 1, gj@ - 1));
                }

                if nums1[i - 1] == nums2[j - 1] {
                    proof {
                        reveal_with_fuel(Solution::lcs_suffix, 2);
                    }
                    let val = dp[prev_idx] + 1;
                    proof {
                        assert(val as int == Self::lcs_suffix(
                            nums1@, nums2@, gi@, gj@));
                        Self::lemma_lcs_suffix_bound(
                            nums1@, nums2@, gi@, gj@);
                    }
                    dp.set(cur_idx, val);
                    proof {
                        assert(dp@[cur_idx as int] == val as int);
                        assert(dp@[gi@ * (gn + 1) + gj@]
                            == Self::lcs_suffix(nums1@, nums2@, gi@, gj@));
                        assert forall |ii: int| #![trigger dp@[ii * (gn + 1)]]
                            0 <= ii <= gm && 0 <= ii * (gn + 1) < gt
                            implies dp@[ii * (gn + 1)] == 0
                        by {
                            Self::lemma_idx_col0_disjoint(gi@, gj@, gn, ii);
                        };
                        assert forall |ii: int, jj: int|
                            ((0 <= ii < i as int && 0 <= jj <= gn)
                                || (ii == i as int && 0 <= jj < j as int))
                            && 0 <= ii * (gn + 1) + jj < gt
                            implies dp@[ii * (gn + 1) + jj]
                                == Self::lcs_suffix(nums1@, nums2@, ii, jj)
                        by {
                            if ii * (gn + 1) + jj == cur_idx as int {
                                Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                            }
                        };
                        assert forall |ii: int, jj: int|
                            ((0 <= ii < i as int && 0 <= jj <= gn)
                                || (ii == i as int && 0 <= jj < j as int))
                            && 0 <= ii * (gn + 1) + jj < gt
                            implies (#[trigger] dp@[ii * (gn + 1) + jj]) <= max_len as int
                        by {
                            if ii * (gn + 1) + jj == cur_idx as int {
                                Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                            }
                        };
                    }
                    if val > max_len {
                        max_len = val;
                        proof { max_ii = gi@; max_jj = gj@; }
                    } else {
                        proof {
                            if max_len as int > 0 {
                                if max_ii * (gn + 1) + max_jj == cur_idx as int {
                                    Self::lemma_flat_idx_injective(gn, max_ii, max_jj, gi@, gj@);
                                    assert(false);
                                }
                            }
                        }
                    }
                } else {
                    proof {
                        reveal_with_fuel(Solution::lcs_suffix, 2);
                        assert(0int == Self::lcs_suffix(
                            nums1@, nums2@, gi@, gj@));
                    }
                    dp.set(cur_idx, 0);
                    proof {
                        assert(dp@[gi@ * (gn + 1) + gj@]
                            == Self::lcs_suffix(nums1@, nums2@, gi@, gj@));
                        assert forall |ii: int| #![trigger dp@[ii * (gn + 1)]]
                            0 <= ii <= gm && 0 <= ii * (gn + 1) < gt
                            implies dp@[ii * (gn + 1)] == 0
                        by {
                            Self::lemma_idx_col0_disjoint(gi@, gj@, gn, ii);
                        };
                        assert forall |ii: int, jj: int|
                            ((0 <= ii < i as int && 0 <= jj <= gn)
                                || (ii == i as int && 0 <= jj < j as int))
                            && 0 <= ii * (gn + 1) + jj < gt
                            implies dp@[ii * (gn + 1) + jj]
                                == Self::lcs_suffix(nums1@, nums2@, ii, jj)
                        by {
                            if ii * (gn + 1) + jj == cur_idx as int {
                                Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                            }
                        };
                        assert forall |ii: int, jj: int|
                            ((0 <= ii < i as int && 0 <= jj <= gn)
                                || (ii == i as int && 0 <= jj < j as int))
                            && 0 <= ii * (gn + 1) + jj < gt
                            implies (#[trigger] dp@[ii * (gn + 1) + jj]) <= max_len as int
                        by {
                            if ii * (gn + 1) + jj == cur_idx as int {
                                Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                            }
                        };
                        if max_len as int > 0 {
                            if max_ii * (gn + 1) + max_jj == cur_idx as int {
                                Self::lemma_flat_idx_injective(gn, max_ii, max_jj, gi@, gj@);
                                assert(false);
                            }
                        }
                    }
                }
                j += 1;
            }
            i += 1;
        }

        proof {
            assert forall |ii: int, jj: int|
                0 <= ii <= gm && 0 <= jj <= gn
                implies Self::lcs_suffix(nums1@, nums2@, ii, jj)
                    <= max_len as int
            by {
                assert(ii < i as int);
                assert(0 <= ii * (gn + 1) + jj < gt)
                    by(nonlinear_arith)
                    requires 0 <= ii <= gm, 0 <= jj <= gn,
                        gt == (gm + 1) * (gn + 1);
                assert(dp@[ii * (gn + 1) + jj]
                    == Self::lcs_suffix(nums1@, nums2@, ii, jj));
                assert((#[trigger] dp@[ii * (gn + 1) + jj])
                    <= max_len as int);
            };

            if max_len as int > 0 {
                assert(dp@[max_ii * (gn + 1) + max_jj] == max_len as int);
                assert(Self::lcs_suffix(nums1@, nums2@, max_ii, max_jj)
                    == max_len as int);
                Self::lemma_lcs_suffix_common_at(nums1@, nums2@, max_ii, max_jj);
                Self::lemma_lcs_suffix_bound(nums1@, nums2@, max_ii, max_jj);
            } else {
                assert(Self::common_at(nums1@, nums2@, 0, 0, 0));
            }

            assert forall |L: int, i: int, j: int|
                (L > max_len as int
                    && Self::common_at(nums1@, nums2@, i, j, L))
                    implies false
            by {
                if L > max_len as int
                    && Self::common_at(nums1@, nums2@, i, j, L) {
                    Self::lemma_max_no_longer(
                        nums1@, nums2@, max_len as int, i, j, L);
                }
            };
        }
        max_len
    }
}

}