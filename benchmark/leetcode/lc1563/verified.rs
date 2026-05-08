use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn range_sum(sv: Seq<int>, i: int, j: int) -> int
        decreases (if j >= i { j - i + 1 } else { 0 })
    {
        if i > j {
            0
        } else {
            sv[i] + Self::range_sum(sv, i + 1, j)
        }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn max_split_score(sv: Seq<int>, i: int, j: int, k: int) -> int
        recommends 0 <= i, i <= k
        decreases j - i, j - k
    {
        if k >= j || k < i {
            0
        } else {
            let dp_left = if i >= k { 0 } else { Self::max_split_score(sv, i, k, i) };
            let dp_right = if k + 1 >= j { 0 } else { Self::max_split_score(sv, k + 1, j, k + 1) };
            let left = Self::range_sum(sv, i, k);
            let right = Self::range_sum(sv, k + 1, j);
            let score = if left < right {
                left + dp_left
            } else if left > right {
                right + dp_right
            } else {
                Self::spec_max(left + dp_left, right + dp_right)
            };
            Self::spec_max(score, Self::max_split_score(sv, i, j, k + 1))
        }
    }

    pub open spec fn optimal_score(sv: Seq<int>, i: int, j: int) -> int {
        if i >= j { 0 }
        else { Self::max_split_score(sv, i, j, i) }
    }

    proof fn lemma_range_sum_split(sv: Seq<int>, i: int, m: int, j: int)
        requires
            0 <= i,
            i <= m + 1,
            m <= j,
            j < sv.len(),
        ensures
            Self::range_sum(sv, i, j) == Self::range_sum(sv, i, m) + Self::range_sum(sv, m + 1, j),
        decreases m - i + 1
    {
        if i > m {
            assert(Self::range_sum(sv, i, m) == 0);
        } else if i == m {
            assert(Self::range_sum(sv, i + 1, m) == 0);
            assert(Self::range_sum(sv, i, m) == sv[i] + Self::range_sum(sv, i + 1, m));
            assert(Self::range_sum(sv, i, j) == sv[i] + Self::range_sum(sv, i + 1, j));
            assert(Self::range_sum(sv, m + 1, j) == Self::range_sum(sv, i + 1, j));
        } else {
            Self::lemma_range_sum_split(sv, i + 1, m, j);
        }
    }

    proof fn lemma_range_sum_bound(sv: Seq<int>, i: int, j: int)
        requires
            0 <= i,
            j < sv.len(),
            forall|k: int| 0 <= k < sv.len() ==> 1 <= #[trigger] sv[k] <= 1_000_000,
        ensures
            i <= j ==> j - i + 1 <= Self::range_sum(sv, i, j) <= (j - i + 1) * 1_000_000,
            i > j ==> Self::range_sum(sv, i, j) == 0,
        decreases (if j >= i { j - i + 1 } else { 0 })
    {
        if i <= j {
            if i < j {
                Self::lemma_range_sum_bound(sv, i + 1, j);
            }
        }
    }

    proof fn lemma_max_split_nonneg(sv: Seq<int>, i: int, j: int, k: int)
        requires
            0 <= i,
            i <= k,
            j < sv.len(),
            forall|kk: int| 0 <= kk < sv.len() ==> 1 <= #[trigger] sv[kk] <= 1_000_000,
        ensures
            Self::max_split_score(sv, i, j, k) >= 0,
        decreases j - i, j - k
    {
        if k < j {
            Self::lemma_max_split_nonneg(sv, i, j, k + 1);
            Self::lemma_range_sum_bound(sv, i, k);
            Self::lemma_range_sum_bound(sv, k + 1, j);
            if i < k {
                Self::lemma_max_split_nonneg(sv, i, k, i);
            }
            if k + 1 < j {
                Self::lemma_max_split_nonneg(sv, k + 1, j, k + 1);
            }
        }
    }

    proof fn lemma_optimal_nonneg(sv: Seq<int>, i: int, j: int)
        requires
            0 <= i,
            j < sv.len(),
            forall|k: int| 0 <= k < sv.len() ==> 1 <= #[trigger] sv[k] <= 1_000_000,
        ensures
            Self::optimal_score(sv, i, j) >= 0,
    {
        if i < j {
            Self::lemma_max_split_nonneg(sv, i, j, i);
        }
    }

    proof fn lemma_max_split_bound(sv: Seq<int>, i: int, j: int, k: int)
        requires
            0 <= i,
            i <= k,
            i < j,
            j < sv.len(),
            forall|kk: int| 0 <= kk < sv.len() ==> 1 <= #[trigger] sv[kk] <= 1_000_000,
        ensures
            Self::max_split_score(sv, i, j, k) < Self::range_sum(sv, i, j),
        decreases j - i, j - k
    {
        if k < j {
            Self::lemma_max_split_bound(sv, i, j, k + 1);
            let left = Self::range_sum(sv, i, k);
            let right = Self::range_sum(sv, k + 1, j);
            Self::lemma_range_sum_split(sv, i, k, j);
            assert(left + right == Self::range_sum(sv, i, j));
            Self::lemma_range_sum_bound(sv, i, k);
            Self::lemma_range_sum_bound(sv, k + 1, j);
            assert(left >= 1);
            assert(right >= 1);

            if i < k {
                Self::lemma_max_split_bound(sv, i, k, i);
                Self::lemma_max_split_nonneg(sv, i, k, i);
            }
            if k + 1 < j {
                Self::lemma_max_split_bound(sv, k + 1, j, k + 1);
                Self::lemma_max_split_nonneg(sv, k + 1, j, k + 1);
            }

            let dp_left = if i >= k { 0int } else { Self::max_split_score(sv, i, k, i) };
            let dp_right = if k + 1 >= j { 0int } else { Self::max_split_score(sv, k + 1, j, k + 1) };
            assert(dp_left >= 0);
            assert(dp_right >= 0);
            assert(dp_left < left) by {
                if i < k {} else {
                    assert(dp_left == 0int);
                }
            };
            assert(dp_right < right) by {
                if k + 1 < j {} else {
                    assert(dp_right == 0int);
                }
            };
            if left < right {
                assert(left + dp_left < left + right);
            } else if left > right {
                assert(right + dp_right < left + right);
            } else {
                assert(left + dp_left < left + right);
                assert(right + dp_right < left + right);
                assert(Self::spec_max(left + dp_left, right + dp_right) < left + right);
            }
        } else {
            Self::lemma_range_sum_bound(sv, i, j);
        }
    }

    proof fn lemma_optimal_bound(sv: Seq<int>, i: int, j: int)
        requires
            0 <= i,
            i < j,
            j < sv.len(),
            forall|k: int| 0 <= k < sv.len() ==> 1 <= #[trigger] sv[k] <= 1_000_000,
        ensures
            Self::optimal_score(sv, i, j) < Self::range_sum(sv, i, j),
    {
        Self::lemma_max_split_bound(sv, i, j, i);
    }

    proof fn lemma_flat_idx_injective(n: int, i1: int, j1: int, i2: int, j2: int)
        requires
            n >= 1,
            0 <= j1 < n,
            0 <= j2 < n,
            0 <= i1,
            0 <= i2,
            i1 * n + j1 == i2 * n + j2,
        ensures
            i1 == i2 && j1 == j2,
    {
        if i1 > i2 {
            assert((i1 - i2) * n == j2 - j1) by (nonlinear_arith)
                requires i1 * n + j1 == i2 * n + j2;
            assert((i1 - i2) * n >= n) by (nonlinear_arith)
                requires i1 > i2, n >= 1;
        } else if i1 < i2 {
            assert((i2 - i1) * n == j1 - j2) by (nonlinear_arith)
                requires i1 * n + j1 == i2 * n + j2;
            assert((i2 - i1) * n >= n) by (nonlinear_arith)
                requires i2 > i1, n >= 1;
        }
    }

    proof fn lemma_flat_idx_bound(n: int, i: int, j: int)
        requires
            n >= 1,
            0 <= i < n,
            0 <= j < n,
        ensures
            0 <= i * n + j < n * n,
    {
        assert(i * n + j >= 0) by (nonlinear_arith) requires i >= 0, n >= 1, j >= 0;
        assert(i * n + j < n * n) by (nonlinear_arith) requires i < n, j < n, n >= 1;
    }

    proof fn lemma_max_assoc(a: int, b: int, c: int)
        ensures
            Self::spec_max(Self::spec_max(a, b), c) == Self::spec_max(a, Self::spec_max(b, c)),
    {}


    #[verifier::loop_isolation(false)]
    pub fn stone_game_v(stone_value: Vec<i32>) -> (result: i32)
        requires
            1 <= stone_value.len() <= 500,
            forall|i: int| 0 <= i < stone_value.len() ==> 1 <= #[trigger] stone_value[i] <= 1_000_000,
        ensures
            result as int == Self::optimal_score(
                stone_value@.map(|_i: int, v: i32| v as int),
                0int,
                stone_value@.len() as int - 1,
            ),
    {
        let n = stone_value.len();
        let ghost sv = stone_value@.map(|_i: int, v: i32| v as int);
        let ghost gn = n as int;

        if n <= 1 {
            return 0;
        }

        proof {
            assert forall|k: int| 0 <= k < gn implies 1 <= #[trigger] sv[k] <= 1_000_000 by {
                assert(stone_value@[k] == stone_value[k]);
            };
        }

        let mut pre: Vec<i64> = Vec::new();
        pre.push(0i64);
        let mut idx: usize = 0;
        while idx < n
            invariant
                gn == n as int,
                1 < n <= 500,
                sv == stone_value@.map(|_i: int, v: i32| v as int),
                sv.len() == gn,
                pre.len() == idx + 1,
                0 <= idx <= n,
                forall|k: int| 0 <= k < gn ==> 1 <= #[trigger] sv[k] <= 1_000_000,
                forall|k: int| 0 <= k <= idx as int ==> (#[trigger] pre@[k]) as int == Self::range_sum(sv, 0, k - 1),
                forall|k: int| 0 <= k <= idx as int ==> 0 <= (#[trigger] pre@[k]) <= 500_000_000i64,
            decreases n - idx
        {
            proof {
                if idx > 0 {
                    Self::lemma_range_sum_split(sv, 0, idx as int - 1, idx as int);
                }
                Self::lemma_range_sum_bound(sv, 0, idx as int);
                assert(idx as int + 1 > idx as int);
                assert(Self::range_sum(sv, idx as int + 1, idx as int) == 0);
                assert(Self::range_sum(sv, idx as int, idx as int) == sv[idx as int] + Self::range_sum(sv, idx as int + 1, idx as int));
                assert(Self::range_sum(sv, idx as int, idx as int) == sv[idx as int]);
                assert(pre@[idx as int] as int + stone_value@[idx as int] as int
                    == Self::range_sum(sv, 0, idx as int - 1) + sv[idx as int]
                    == Self::range_sum(sv, 0, idx as int));
                assert(0 <= Self::range_sum(sv, 0, idx as int)
                    <= (idx as int + 1) * 1_000_000);
                assert((idx as int + 1) * 1_000_000 <= 500_000_000) by (nonlinear_arith)
                    requires idx as int + 1 <= 500;
            }
            pre.push(pre[idx] + stone_value[idx] as i64);
            idx = idx + 1;
        }

        let mut dp: Vec<i32> = Vec::new();
        idx = 0;

        proof {
            assert((n as int) * (n as int) <= 250_000) by (nonlinear_arith)
                requires (n as int) <= 500;
        }

        while idx < n * n
            invariant
                n <= 500,
                (n as int) * (n as int) <= 250_000,
                idx <= n * n,
                dp.len() == idx,
                forall|k: int| 0 <= k < idx as int ==> dp@[k] == 0i32,
            decreases n * n - idx
        {
            dp.push(0i32);
            idx = idx + 1;
        }

        proof {
            assert(dp@.len() == gn * gn) by (nonlinear_arith)
                requires dp@.len() as int == (n * n) as int, gn == n as int, (n as int) * (n as int) <= 250_000;
            assert forall|ii: int, jj: int|
                0 <= ii < gn && 0 <= jj < gn
                implies 0 <= #[trigger] (ii * gn + jj) && ii * gn + jj < dp@.len() by {
                Self::lemma_flat_idx_bound(gn, ii, jj);
            };
            assert forall|ii: int, jj: int|
                0 <= ii < gn && ii <= jj && jj < gn && jj - ii < 1
                implies (#[trigger] dp@[ii * gn + jj]) as int == Self::optimal_score(sv, ii, jj) by {
                assert(jj == ii);
                Self::lemma_flat_idx_bound(gn, ii, jj);
            };
            assert forall|ii: int, jj: int|
                0 <= ii < gn && ii <= jj && jj < gn && jj - ii < 1
                implies 0 <= (#[trigger] dp@[ii * gn + jj]) as int by {
                assert(jj == ii);
                Self::lemma_flat_idx_bound(gn, ii, jj);
            };
        }

        let mut gap: usize = 1;
        while gap < n
            invariant
                gn == n as int,
                1 < n <= 500,
                sv == stone_value@.map(|_i: int, v: i32| v as int),
                sv.len() == gn,
                dp.len() == n * n,
                dp@.len() == gn * gn,
                pre.len() == n + 1,
                1 <= gap <= n,
                forall|k: int| 0 <= k < gn ==> 1 <= #[trigger] sv[k] <= 1_000_000,
                forall|k: int| 0 <= k <= gn ==> (#[trigger] pre@[k]) as int == Self::range_sum(sv, 0, k - 1),
                forall|k: int| 0 <= k <= gn ==> 0 <= (#[trigger] pre@[k]) <= 500_000_000i64,
                forall|ii: int, jj: int|
                    0 <= ii < gn && 0 <= jj < gn
                    ==> 0 <= #[trigger] (ii * gn + jj) && ii * gn + jj < dp@.len(),
                forall|ii: int, jj: int|
                    0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                    ==> (#[trigger] dp@[ii * gn + jj]) as int == Self::optimal_score(sv, ii, jj),
                forall|ii: int, jj: int|
                    0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                    ==> 0 <= (#[trigger] dp@[ii * gn + jj]) as int,
                forall|ii: int, jj: int|
                    0 <= ii < gn && ii < jj && jj < gn && jj - ii < gap as int
                    ==> Self::range_sum(sv, ii, jj) > (#[trigger] dp@[ii * gn + jj]) as int,
            decreases n - gap
        {
            let mut i: usize = 0;
            while i + gap < n
                invariant
                    gn == n as int,
                    1 < n <= 500,
                    sv == stone_value@.map(|_i: int, v: i32| v as int),
                    sv.len() == gn,
                    dp.len() == n * n,
                    dp@.len() == gn * gn,
                    pre.len() == n + 1,
                    1 <= gap < n,
                    0 <= i,
                    i + gap <= n,
                    forall|k: int| 0 <= k < gn ==> 1 <= #[trigger] sv[k] <= 1_000_000,
                    forall|k: int| 0 <= k <= gn ==> (#[trigger] pre@[k]) as int == Self::range_sum(sv, 0, k - 1),
                    forall|k: int| 0 <= k <= gn ==> 0 <= (#[trigger] pre@[k]) <= 500_000_000i64,
                    forall|ii: int, jj: int|
                        0 <= ii < gn && 0 <= jj < gn
                        ==> 0 <= #[trigger] (ii * gn + jj) && ii * gn + jj < dp@.len(),
                    forall|ii: int, jj: int|
                        0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                        ==> (#[trigger] dp@[ii * gn + jj]) as int == Self::optimal_score(sv, ii, jj),
                    forall|ii: int, jj: int|
                        0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                        ==> 0 <= (#[trigger] dp@[ii * gn + jj]) as int,
                    forall|ii: int, jj: int|
                        0 <= ii < gn && ii < jj && jj < gn && jj - ii < gap as int
                        ==> Self::range_sum(sv, ii, jj) > (#[trigger] dp@[ii * gn + jj]) as int,
                    forall|ii: int|
                        0 <= ii < i as int
                        ==> (#[trigger] dp@[ii * gn + (ii + gap as int)]) as int == Self::optimal_score(sv, ii, ii + gap as int),
                    forall|ii: int|
                        0 <= ii < i as int
                        ==> 0 <= (#[trigger] dp@[ii * gn + (ii + gap as int)]) as int,
                    forall|ii: int|
                        0 <= ii < i as int
                        ==> Self::range_sum(sv, ii, ii + gap as int) > (#[trigger] dp@[ii * gn + (ii + gap as int)]) as int,
                decreases n - gap - i
            {
                let j: usize = i + gap;
                let gi: Ghost<int> = Ghost(i as int);
                let gj: Ghost<int> = Ghost(j as int);
                let mut best: i32 = 0;
                let mut k: usize = i;

                proof {
                    Self::lemma_optimal_nonneg(sv, gi@, gj@);
                }

                while k < j
                    invariant
                        gn == n as int,
                        1 < n <= 500,
                        gi@ == i as int,
                        gj@ == j as int,
                        j == i + gap,
                        i + gap < n,
                        sv == stone_value@.map(|_i: int, v: i32| v as int),
                        sv.len() == gn,
                        dp.len() == n * n,
                        dp@.len() == gn * gn,
                        pre.len() == n + 1,
                        1 <= gap < n,
                        0 <= i,
                        i <= k <= j,
                        forall|kk: int| 0 <= kk < gn ==> 1 <= #[trigger] sv[kk] <= 1_000_000,
                        forall|kk: int| 0 <= kk <= gn ==> (#[trigger] pre@[kk]) as int == Self::range_sum(sv, 0, kk - 1),
                        forall|kk: int| 0 <= kk <= gn ==> 0 <= (#[trigger] pre@[kk]) <= 500_000_000i64,
                        forall|ii: int, jj: int|
                            0 <= ii < gn && 0 <= jj < gn
                            ==> 0 <= #[trigger] (ii * gn + jj) && ii * gn + jj < dp@.len(),
                        forall|ii: int, jj: int|
                            0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                            ==> (#[trigger] dp@[ii * gn + jj]) as int == Self::optimal_score(sv, ii, jj),
                        forall|ii: int, jj: int|
                            0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                            ==> 0 <= (#[trigger] dp@[ii * gn + jj]) as int,
                        forall|ii: int, jj: int|
                            0 <= ii < gn && ii < jj && jj < gn && jj - ii < gap as int
                            ==> Self::range_sum(sv, ii, jj) > (#[trigger] dp@[ii * gn + jj]) as int,
                        best >= 0,
                        Self::spec_max(best as int, Self::max_split_score(sv, gi@, gj@, k as int))
                            == Self::optimal_score(sv, gi@, gj@),
                    decreases j - k
                {
                    let gk: Ghost<int> = Ghost(k as int);

                    proof {
                        Self::lemma_flat_idx_bound(gn, gi@, gk@);
                        Self::lemma_flat_idx_bound(gn, gk@ + 1, gj@);

                        assert(dp@[gi@ * gn + gk@] as int == Self::optimal_score(sv, gi@, gk@));
                        assert(dp@[(gk@ + 1) * gn + gj@] as int == Self::optimal_score(sv, gk@ + 1, gj@));

                        Self::lemma_range_sum_bound(sv, gi@, gk@);
                        Self::lemma_range_sum_bound(sv, gk@ + 1, gj@);
                        Self::lemma_range_sum_bound(sv, gi@, gj@);

                        if gi@ < gk@ {
                            Self::lemma_optimal_bound(sv, gi@, gk@);
                        } else {
                            Self::lemma_optimal_nonneg(sv, gi@, gk@);
                        }
                        if gk@ + 1 < gj@ {
                            Self::lemma_optimal_bound(sv, gk@ + 1, gj@);
                        } else {
                            Self::lemma_optimal_nonneg(sv, gk@ + 1, gj@);
                        }
                    }

                    let left_sum: i64 = pre[k + 1] - pre[i];
                    let right_sum: i64 = pre[j + 1] - pre[k + 1];

                    proof {
                        if gi@ > 0 {
                            Self::lemma_range_sum_split(sv, 0, gi@ - 1, gk@);
                        }
                        Self::lemma_range_sum_split(sv, 0, gk@, gj@);

                        assert(left_sum as int == Self::range_sum(sv, gi@, gk@));
                        assert(right_sum as int == Self::range_sum(sv, gk@ + 1, gj@));
                    }

                    let ghost spec_left = Self::range_sum(sv, gi@, gk@);
                    let ghost spec_right = Self::range_sum(sv, gk@ + 1, gj@);
                    let ghost spec_dp_left = Self::optimal_score(sv, gi@, gk@);
                    let ghost spec_dp_right = Self::optimal_score(sv, gk@ + 1, gj@);

                    let score: i32;
                    if left_sum < right_sum {
                        proof {
                            assert(spec_left + spec_dp_left >= 1);
                            if gi@ < gk@ {
                                assert(spec_dp_left < spec_left);
                            }
                            assert(spec_left + spec_dp_left < 2 * spec_left);
                            assert(spec_left <= 500_000_000);
                            assert(2 * spec_left <= 1_000_000_000) by (nonlinear_arith)
                                requires spec_left <= 500_000_000;
                            assert(i32::MIN <= spec_left + spec_dp_left <= i32::MAX) by (nonlinear_arith)
                                requires
                                    0 <= spec_dp_left,
                                    spec_left + spec_dp_left < 2 * spec_left,
                                    2 * spec_left <= 1_000_000_000;
                        }
                        score = left_sum as i32 + dp[i * n + k];
                    } else if left_sum > right_sum {
                        proof {
                            assert(spec_right + spec_dp_right >= 1);
                            if gk@ + 1 < gj@ {
                                assert(spec_dp_right < spec_right);
                            }
                            assert(spec_right + spec_dp_right < 2 * spec_right);
                            assert(spec_right <= 500_000_000);
                            assert(2 * spec_right <= 1_000_000_000) by (nonlinear_arith)
                                requires spec_right <= 500_000_000;
                            assert(i32::MIN <= spec_right + spec_dp_right <= i32::MAX) by (nonlinear_arith)
                                requires
                                    0 <= spec_dp_right,
                                    spec_right + spec_dp_right < 2 * spec_right,
                                    2 * spec_right <= 1_000_000_000;
                        }
                        score = right_sum as i32 + dp[(k + 1) * n + j];
                    } else {
                        proof {
                            assert(spec_left == spec_right);
                            assert(spec_left <= 500_000_000);
                            assert(2 * spec_left <= 1_000_000_000) by (nonlinear_arith)
                                requires spec_left <= 500_000_000;
                            assert(i32::MIN <= spec_left + spec_dp_left <= i32::MAX) by (nonlinear_arith)
                                requires
                                    0 <= spec_dp_left,
                                    spec_left + spec_dp_left < 2 * spec_left || gi@ == gk@,
                                    2 * spec_left <= 1_000_000_000,
                                    spec_left >= 1,
                                    gi@ == gk@ ==> spec_dp_left == 0;
                            assert(i32::MIN <= spec_right + spec_dp_right <= i32::MAX) by (nonlinear_arith)
                                requires
                                    0 <= spec_dp_right,
                                    spec_right + spec_dp_right < 2 * spec_right || gk@ + 1 == gj@,
                                    2 * spec_right <= 1_000_000_000,
                                    spec_right >= 1,
                                    gk@ + 1 == gj@ ==> spec_dp_right == 0;
                        }
                        let a: i32 = left_sum as i32 + dp[i * n + k];
                        let b: i32 = right_sum as i32 + dp[(k + 1) * n + j];
                        if a >= b {
                            score = a;
                        } else {
                            score = b;
                        }
                    }

                    let ghost old_best_val = best as int;

                    proof {
                        let spec_score = if spec_left < spec_right {
                            spec_left + spec_dp_left
                        } else if spec_left > spec_right {
                            spec_right + spec_dp_right
                        } else {
                            Self::spec_max(spec_left + spec_dp_left, spec_right + spec_dp_right)
                        };
                        assert(score as int == spec_score);

                        let rest = Self::max_split_score(sv, gi@, gj@, gk@ + 1);
                        assert(Self::max_split_score(sv, gi@, gj@, gk@) == Self::spec_max(spec_score, rest));

                        Self::lemma_max_split_nonneg(sv, gi@, gj@, gk@ + 1);

                        Self::lemma_max_assoc(old_best_val, spec_score, rest);
                    }

                    if score > best {
                        best = score;
                    }

                    proof {
                        assert(best as int == Self::spec_max(old_best_val, score as int));
                    }

                    k = k + 1;
                }

                proof {
                    assert(Self::max_split_score(sv, gi@, gj@, gj@) == 0int);
                    assert(best as int == Self::optimal_score(sv, gi@, gj@));

                    Self::lemma_flat_idx_bound(gn, gi@, gj@);
                    Self::lemma_optimal_bound(sv, gi@, gj@);
                    Self::lemma_range_sum_bound(sv, gi@, gj@);
                }

                let ghost old_dp = dp@;
                dp.set(i * n + j, best);

                proof {
                    assert(dp@[gi@ * gn + gj@] as int == Self::optimal_score(sv, gi@, gj@));

                    assert forall|ii: int, jj: int|
                        0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                        implies (#[trigger] dp@[ii * gn + jj]) as int == Self::optimal_score(sv, ii, jj) by {
                        if ii * gn + jj == gi@ * gn + gj@ {
                            Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                        }
                    };
                    assert forall|ii: int, jj: int|
                        0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int
                        implies 0 <= (#[trigger] dp@[ii * gn + jj]) as int by {
                        if ii * gn + jj == gi@ * gn + gj@ {
                            Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                        }
                    };
                    assert forall|ii: int, jj: int|
                        0 <= ii < gn && ii < jj && jj < gn && jj - ii < gap as int
                        implies Self::range_sum(sv, ii, jj) > (#[trigger] dp@[ii * gn + jj]) as int by {
                        if ii * gn + jj == gi@ * gn + gj@ {
                            Self::lemma_flat_idx_injective(gn, ii, jj, gi@, gj@);
                        }
                    };

                    assert forall|ii: int|
                        0 <= ii < i as int + 1
                        implies (#[trigger] dp@[ii * gn + (ii + gap as int)]) as int == Self::optimal_score(sv, ii, ii + gap as int) by {
                        if ii == i as int {
                            assert(dp@[gi@ * gn + gj@] as int == Self::optimal_score(sv, gi@, gj@));
                        } else {
                            if ii * gn + (ii + gap as int) == gi@ * gn + gj@ {
                                Self::lemma_flat_idx_injective(gn, ii, ii + gap as int, gi@, gj@);
                            }
                        }
                    };
                    assert forall|ii: int|
                        0 <= ii < i as int + 1
                        implies 0 <= (#[trigger] dp@[ii * gn + (ii + gap as int)]) as int by {
                        if ii == i as int {
                        } else {
                            if ii * gn + (ii + gap as int) == gi@ * gn + gj@ {
                                Self::lemma_flat_idx_injective(gn, ii, ii + gap as int, gi@, gj@);
                            }
                        }
                    };
                    assert forall|ii: int|
                        0 <= ii < i as int + 1
                        implies Self::range_sum(sv, ii, ii + gap as int) > (#[trigger] dp@[ii * gn + (ii + gap as int)]) as int by {
                        if ii == i as int {
                        } else {
                            if ii * gn + (ii + gap as int) == gi@ * gn + gj@ {
                                Self::lemma_flat_idx_injective(gn, ii, ii + gap as int, gi@, gj@);
                            }
                        }
                    };
                }

                i = i + 1;
            }

            proof {
                assert forall|ii: int, jj: int|
                    0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int + 1
                    implies (#[trigger] dp@[ii * gn + jj]) as int == Self::optimal_score(sv, ii, jj) by {
                    if jj - ii == gap as int {
                        assert(jj == ii + gap as int);
                        assert(ii < i as int);
                        assert(dp@[ii * gn + (ii + gap as int)] as int == Self::optimal_score(sv, ii, ii + gap as int));
                    }
                };
                assert forall|ii: int, jj: int|
                    0 <= ii < gn && ii <= jj && jj < gn && jj - ii < gap as int + 1
                    implies 0 <= (#[trigger] dp@[ii * gn + jj]) as int by {
                    if jj - ii == gap as int {
                        assert(jj == ii + gap as int);
                        assert(ii < i as int);
                        assert(0 <= dp@[ii * gn + (ii + gap as int)] as int);
                    }
                };
                assert forall|ii: int, jj: int|
                    0 <= ii < gn && ii < jj && jj < gn && jj - ii < gap as int + 1
                    implies Self::range_sum(sv, ii, jj) > (#[trigger] dp@[ii * gn + jj]) as int by {
                    if jj - ii == gap as int {
                        assert(jj == ii + gap as int);
                        assert(ii < i as int);
                        assert(dp@[ii * gn + (ii + gap as int)] as int == Self::optimal_score(sv, ii, ii + gap as int));
                        Self::lemma_optimal_bound(sv, ii, jj);
                    }
                };
            }

            gap = gap + 1;
        }

        proof {
            Self::lemma_flat_idx_bound(gn, 0, gn - 1);
            assert(dp@[0 * gn + (gn - 1)] == dp@[gn - 1]);
            assert(dp@[gn - 1] as int == Self::optimal_score(sv, 0, gn - 1));
        }

        dp[n - 1]
    }
}

}