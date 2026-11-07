use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_sum(piles: Seq<i32>, i: int) -> int
        decreases piles.len() - i
    {
        if i >= piles.len() {
            0
        } else {
            piles[i] as int + Self::suffix_sum(piles, i + 1)
        }
    }

    pub open spec fn game(piles: Seq<i32>, i: int, m: int, k: int) -> int
        decreases piles.len() - i, k
        when m >= 1 && k >= 0 && i >= 0
            && (1 <= k && k <= 2 * m ==> i + 2 * m < piles.len())
    {
        if k > 2 * m {
            if i >= piles.len() {
                0
            } else if i + 2 * m >= piles.len() {
                Self::suffix_sum(piles, i)
            } else {
                Self::game(piles, i, m, 2 * m)
            }
        } else if k == 0 {
            0
        } else {
            let new_m = if k > m { k } else { m };
            let score_k = Self::suffix_sum(piles, i)
                - Self::game(piles, i + k, new_m, 2 * new_m + 1);
            if k == 1 {
                score_k
            } else {
                let prev = Self::game(piles, i, m, k - 1);
                if score_k >= prev { score_k } else { prev }
            }
        }
    }

    pub open spec fn optimal(piles: Seq<i32>, i: int, m: int) -> int
    {
        Self::game(piles, i, m, 2 * m + 1)
    }

    pub open spec fn max_score(piles: Seq<i32>, i: int, m: int, k: int) -> int
    {
        Self::game(piles, i, m, k)
    }

    proof fn lemma_suffix_sum_bounds(piles: Seq<i32>, i: int)
        requires
            0 <= i <= piles.len(),
            piles.len() <= 100,
            forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
        ensures
            0 <= Self::suffix_sum(piles, i) <= (piles.len() - i) * 10000,
        decreases piles.len() - i
    {
        if i < piles.len() {
            Self::lemma_suffix_sum_bounds(piles, i + 1);
            assert(10000 + (piles.len() - i - 1) * 10000 == (piles.len() - i) * 10000) by (nonlinear_arith)
                requires piles.len() - i >= 1 {}
        }
    }

    proof fn lemma_suffix_sum_monotone(piles: Seq<i32>, i: int, j: int)
        requires
            0 <= i <= j <= piles.len(),
            forall |k: int| 0 <= k < piles.len() ==> 1 <= #[trigger] piles[k] <= 10000,
        ensures
            Self::suffix_sum(piles, j) <= Self::suffix_sum(piles, i),
        decreases j - i
    {
        if i < j {
            Self::lemma_suffix_sum_monotone(piles, i + 1, j);
        }
    }

    proof fn lemma_game_bounds(piles: Seq<i32>, i: int, m: int, k: int)
        requires
            m >= 1, k >= 0, i >= 0, i <= piles.len(),
            k <= 2 * m ==> i + 2 * m < piles.len(),
            piles.len() <= 100,
            forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
        ensures
            0 <= Self::game(piles, i, m, k) <= Self::suffix_sum(piles, i),
        decreases piles.len() - i, k
    {
        if k > 2 * m {
            if i >= piles.len() {
            } else if i + 2 * m >= piles.len() {
                Self::lemma_suffix_sum_bounds(piles, i);
            } else {
                Self::lemma_game_bounds(piles, i, m, 2 * m);
            }
        } else if k == 0 {
            Self::lemma_suffix_sum_bounds(piles, i);
        } else {
            let new_m = if k > m { k } else { m };
            assert(new_m >= 1);
            assert(i + k >= 1);
            assert(i + k <= i + 2 * m);
            assert(i + 2 * m < piles.len());
            assert(i + k <= piles.len());
            Self::lemma_game_bounds(piles, i + k, new_m, 2 * new_m + 1);
            Self::lemma_suffix_sum_monotone(piles, i, i + k);
            Self::lemma_suffix_sum_bounds(piles, i);
            if k > 1 {
                Self::lemma_game_bounds(piles, i, m, k - 1);
            }
        }
    }

    proof fn lemma_optimal_bounds(piles: Seq<i32>, i: int, m: int)
        requires
            0 <= i <= piles.len(),
            m >= 1,
            piles.len() <= 100,
            forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
        ensures
            0 <= Self::optimal(piles, i, m) <= Self::suffix_sum(piles, i),
    {
        Self::lemma_game_bounds(piles, i, m, 2 * m + 1);
    }

    proof fn lemma_max_score_bounds(piles: Seq<i32>, i: int, m: int, k: int)
        requires
            0 <= i < piles.len(),
            i + 2 * m < piles.len(),
            1 <= k <= 2 * m,
            m >= 1,
            piles.len() <= 100,
            forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
        ensures
            0 <= Self::max_score(piles, i, m, k) <= Self::suffix_sum(piles, i),
    {
        Self::lemma_game_bounds(piles, i, m, k);
    }

    proof fn lemma_flat_idx_bound(i: int, m: int, n: int)
        requires
            0 <= i <= n,
            0 <= m <= n,
            n <= 100,
        ensures
            0 <= i * (n + 1) + m,
            i * (n + 1) + m < (n + 1) * (n + 1),
            i * (n + 1) + m <= 10200,
            i * (n + 1) <= 10100,
    {
        assert(i * (n + 1) >= 0) by (nonlinear_arith) requires 0 <= i, 0 <= n {}
        assert(i * (n + 1) <= n * (n + 1)) by (nonlinear_arith) requires 0 <= i <= n, 0 <= n {}
        assert(n * (n + 1) <= 10100) by (nonlinear_arith) requires 0 <= n, n <= 100 {}
        assert(i * (n + 1) + m >= 0) by (nonlinear_arith) requires i * (n + 1) >= 0, m >= 0 {}
        assert(i * (n + 1) + m <= n * (n + 1) + n) by (nonlinear_arith) requires 0 <= i <= n, 0 <= m <= n, 0 <= n {}
        assert(n * (n + 1) + n == (n + 1) * (n + 1) - 1) by (nonlinear_arith) requires 0 <= n {}
        assert((n + 1) * (n + 1) - 1 <= 10200) by (nonlinear_arith) requires 0 <= n, n <= 100 {}
    }

    proof fn lemma_flat_idx_ne_higher_row(i1: int, m1: int, i2: int, m2: int, n: int)
        requires
            0 <= i1 < i2 <= n,
            0 <= m1 <= n,
            0 <= m2 <= n,
            n <= 100,
        ensures
            i1 * (n + 1) + m1 != i2 * (n + 1) + m2,
    {
        assert(i2 * (n + 1) + m2 >= (i1 + 1) * (n + 1)) by (nonlinear_arith)
            requires i2 >= i1 + 1, m2 >= 0, n >= 0 {}
        assert((i1 + 1) * (n + 1) == i1 * (n + 1) + (n + 1)) by (nonlinear_arith)
            requires n >= 0 {}
        assert(i1 * (n + 1) + m1 <= i1 * (n + 1) + n) by (nonlinear_arith)
            requires m1 <= n {}
        assert(i1 * (n + 1) + n < i1 * (n + 1) + (n + 1)) by (nonlinear_arith)
            requires n >= 0 {}
    }

    proof fn lemma_flat_idx_ne_same_row(i: int, m1: int, m2: int, n: int)
        requires
            0 <= i <= n,
            0 <= m1 <= n,
            0 <= m2 <= n,
            m1 != m2,
            n <= 100,
        ensures
            i * (n + 1) + m1 != i * (n + 1) + m2,
    {}

    spec fn flat(i: int, m: int, n: int) -> int {
        i * (n + 1) + m
    }

    pub fn stone_game_ii(piles: Vec<i32>) -> (result: i32)
        requires
            1 <= piles.len() <= 100,
            forall |i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
        ensures
            result as int == Self::optimal(piles@, 0, 1),
    {
        let n = piles.len();
        let stride = n + 1;
        let ghost ni = n as int;

        let mut suffix_sums: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < stride
            invariant
                k <= stride,
                stride == n + 1,
                suffix_sums.len() == k as int,
                forall |j: int| 0 <= j < k as int ==> suffix_sums@[j] == 0i32,
            decreases stride - k
        {
            suffix_sums.push(0i32);
            k += 1;
        }

        let mut si = n;
        while si > 0
            invariant
                0 <= si <= n,
                n == piles.len(),
                suffix_sums.len() == stride as int,
                stride == n + 1,
                piles.len() <= 100,
                forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
                forall |j: int| si as int <= j <= n as int
                    ==> suffix_sums@[j] as int == Self::suffix_sum(piles@, j),
            decreases si
        {
            si -= 1;
            proof {
                Self::lemma_suffix_sum_bounds(piles@, si as int + 1);
                Self::lemma_suffix_sum_bounds(piles@, si as int);
                assert((piles@.len() - si as int) * 10000 <= 1_000_000) by (nonlinear_arith)
                    requires piles@.len() <= 100, si as int >= 0 {}
            }
            suffix_sums.set(si, suffix_sums[si + 1] + piles[si]);
        }

        proof {
            assert(stride <= 101usize);
            assert((stride as int) * (stride as int) <= 10201) by (nonlinear_arith)
                requires stride as int >= 0, stride as int <= 101 {}
        }
        let total = stride * stride;

        let mut dp: Vec<i32> = Vec::new();
        let mut k2: usize = 0;
        while k2 < total
            invariant
                k2 <= total,
                total == stride * stride,
                stride == n + 1,
                n <= 100,
                dp.len() == k2 as int,
                forall |j: int| 0 <= j < k2 as int ==> dp@[j] == 0i32,
            decreases total - k2
        {
            dp.push(0i32);
            k2 += 1;
        }

        proof {
            assert(dp@.len() == (ni + 1) * (ni + 1)) by {
                assert(dp@.len() == total as int);
                assert(total as int == (stride as int) * (stride as int));
                assert(stride as int == ni + 1);
                assert((stride as int) * (stride as int) == (ni + 1) * (ni + 1));
            }
            
            assert forall |j: int, mm: int|
                ni <= j <= ni && 1 <= mm <= ni
                implies dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm)
            by {
                assert(j == ni);
                Self::lemma_flat_idx_bound(j, mm, ni);
                assert(Self::flat(j, mm, ni) < total as int) by {
                    assert(j * (ni + 1) + mm < (ni + 1) * (ni + 1));
                    assert(total as int == (stride as int) * (stride as int));
                    assert(stride as int == ni + 1);
                }
                assert(dp@[Self::flat(j, mm, ni)] == 0i32);
                assert(ni == piles@.len());
                assert(j >= piles@.len());
            };
        }

        let mut i: usize = n;
        while i > 0
            invariant
                0 <= i,
                i <= n,
                n == piles.len(),
                n >= 1,
                stride == n + 1,
                total == stride * stride,
                stride <= 101,
                ni == n as int,
                dp.len() == total as int,
                dp@.len() == (ni + 1) * (ni + 1),
                suffix_sums.len() == stride as int,
                piles.len() <= 100,
                forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
                forall |j: int| 0 <= j <= n as int
                    ==> suffix_sums@[j] as int == Self::suffix_sum(piles@, j),
                forall |j: int, mm: int|
                    i as int <= j <= ni && 1 <= mm <= ni
                    ==> dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm),
            decreases i
        {
            i -= 1;

            let mut m: usize = 1;

            while m <= n
                invariant
                    0 <= i,
                    i < n,
                    n == piles.len(),
                    n >= 1,
                    stride == n + 1,
                    total == stride * stride,
                    stride <= 101,
                    ni == n as int,
                    dp.len() == total as int,
                    dp@.len() == (ni + 1) * (ni + 1),
                    suffix_sums.len() == stride as int,                    1 <= m,
                    m <= n + 1,
                    piles.len() <= 100,
                    forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
                    forall |j: int| 0 <= j <= n as int
                        ==> suffix_sums@[j] as int == Self::suffix_sum(piles@, j),
                    forall |j: int, mm: int|
                        (i as int + 1) <= j <= ni && 1 <= mm <= ni
                        ==> dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm),
                    forall |mm: int|
                        1 <= mm < m as int
                        ==> dp@[Self::flat(i as int, mm, ni)] as int == Self::optimal(piles@, i as int, mm),
                decreases n - m + 1
            {
                proof {
                    assert(i as int <= ni);
                    assert(m as int <= ni);
                    Self::lemma_flat_idx_bound(i as int, m as int, ni);
                }

                if i + 2 * m >= n {
                    proof {
                        Self::lemma_suffix_sum_bounds(piles@, i as int);
                        assert((piles@.len() - i as int) * 10000 <= 1_000_000) by (nonlinear_arith)
                            requires piles@.len() <= 100, i as int >= 0 {}
                        assert(i as int + 2 * (m as int) >= piles@.len());
                    }
                    let ghost old_dp = dp@;
                    dp.set(i * stride + m, suffix_sums[i]);
                    proof {
                        let ghost ii = i as int;
                        let ghost mi = m as int;
                        let ghost idx = Self::flat(ii, mi, ni);
                        assert(idx == (i * stride + m) as int) by {
                            assert(stride as int == ni + 1);
                        }
                        assert(dp@[idx] as int == suffix_sums@[ii] as int);
                        assert(suffix_sums@[ii] as int == Self::suffix_sum(piles@, ii));
                        assert(dp@[idx] as int == Self::optimal(piles@, ii, mi));
                        assert forall |j: int, mm: int|
                            (ii + 1) <= j <= ni && 1 <= mm <= ni
                            implies dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm)
                        by {
                            Self::lemma_flat_idx_bound(j, mm, ni);
                            Self::lemma_flat_idx_ne_higher_row(ii, mi, j, mm, ni);
                            assert(Self::flat(j, mm, ni) != idx);
                            assert(dp@[Self::flat(j, mm, ni)] == old_dp[Self::flat(j, mm, ni)]);
                        }
                        assert forall |mm: int|
                            1 <= mm < mi
                            implies dp@[Self::flat(ii, mm, ni)] as int == Self::optimal(piles@, ii, mm)
                        by {
                            Self::lemma_flat_idx_bound(ii, mm, ni);
                            Self::lemma_flat_idx_ne_same_row(ii, mm, mi, ni);
                            assert(Self::flat(ii, mm, ni) != idx);
                            assert(dp@[Self::flat(ii, mm, ni)] == old_dp[Self::flat(ii, mm, ni)]);
                        }
                    }
                } else {
                    proof {
                        let ghost ii = i as int;
                        let ghost mi = m as int;
                        Self::lemma_suffix_sum_bounds(piles@, ii);
                        assert((piles@.len() - ii) * 10000 <= 1_000_000) by (nonlinear_arith)
                            requires piles@.len() <= 100, ii >= 0 {}
                        assert(ii + 1 <= ni);
                        Self::lemma_optimal_bounds(piles@, ii + 1, mi);
                        Self::lemma_suffix_sum_monotone(piles@, ii, ii + 1);
                        Self::lemma_flat_idx_bound(ii + 1, mi, ni);
                        assert(Self::flat(ii + 1, mi, ni) == ((i + 1) * stride + m) as int) by {
                            assert(stride as int == ni + 1);
                        }
                    }
                    let mut best: i32 = suffix_sums[i] - dp[(i + 1) * stride + m];
                    proof {
                        let ghost ii = i as int;
                        let ghost mi = m as int;
                        assert(dp@[Self::flat(ii + 1, mi, ni)] as int
                            == Self::optimal(piles@, ii + 1, mi));
                        assert(best as int == Self::suffix_sum(piles@, ii)
                            - Self::optimal(piles@, ii + 1, mi));
                        assert(best as int == Self::max_score(piles@, ii, mi, 1));
                        Self::lemma_max_score_bounds(piles@, ii, mi, 1);
                    }
                    let mut x: usize = 2;
                    while x <= 2 * m
                        invariant
                            0 <= i,
                            i < n,
                            n == piles.len(),
                            n >= 1,
                            stride == n + 1,
                            total == stride * stride,
                            stride <= 101,
                            ni == n as int,
                            dp.len() == total as int,
                            dp@.len() == (ni + 1) * (ni + 1),
                            suffix_sums.len() == stride as int,
                            1 <= m,
                            m <= n,
                            i + 2 * m < n,
                            2 <= x,
                            x <= 2 * m + 1,
                            piles.len() <= 100,
                            forall |j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] <= 10000,
                            forall |j: int| 0 <= j <= n as int
                                ==> suffix_sums@[j] as int == Self::suffix_sum(piles@, j),
                            forall |j: int, mm: int|
                                (i as int + 1) <= j <= ni && 1 <= mm <= ni
                                ==> dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm),
                            best as int == Self::max_score(piles@, i as int, m as int, (x - 1) as int),
                            0 <= best as int,
                            best as int <= 1_000_000,
                        decreases 2 * m - x + 1
                    {
                        let new_m: usize = if x > m { x } else { m };
                        proof {
                            let ghost ii = i as int;
                            let ghost mi = m as int;
                            let ghost xi = x as int;
                            let ghost new_mi: int = if xi > mi { xi } else { mi };
                            assert(new_m as int == new_mi);
                            assert(new_mi >= 1);
                            assert(xi <= 2 * mi);
                            assert(new_mi <= 2 * mi);
                            assert(ii >= 0);
                            assert(ii + 2 * mi < ni);
                            assert(2 * mi < ni);
                            assert(new_mi < ni);
                            assert(new_mi <= ni);
                            assert(ii + xi <= ii + 2 * mi);
                            assert(ii + xi < ni);
                            assert(ii + xi <= ni);
                            Self::lemma_flat_idx_bound(ii + xi, new_mi, ni);
                            assert(Self::flat(ii + xi, new_mi, ni) == ((i + x) * stride + new_m) as int) by {
                                assert(stride as int == ni + 1);
                            }
                            Self::lemma_suffix_sum_bounds(piles@, ii);
                            assert((piles@.len() - ii) * 10000 <= 1_000_000) by (nonlinear_arith)
                                requires piles@.len() <= 100, ii >= 0 {}
                            Self::lemma_optimal_bounds(piles@, ii + xi, new_mi);
                            Self::lemma_suffix_sum_monotone(piles@, ii, ii + xi);
                        }
                        let score: i32 = suffix_sums[i] - dp[(i + x) * stride + new_m];
                        if score > best {
                            best = score;
                        }
                        proof {
                            let ghost ii = i as int;
                            let ghost mi = m as int;
                            let ghost xi = x as int;
                            let ghost new_mi: int = if xi > mi { xi } else { mi };
                            assert(dp@[Self::flat(ii + xi, new_mi, ni)] as int
                                == Self::optimal(piles@, ii + xi, new_mi));
                            let ghost score_x = Self::suffix_sum(piles@, ii)
                                - Self::optimal(piles@, ii + xi, new_mi);
                            assert(score as int == score_x);
                            let ghost prev = Self::max_score(piles@, ii, mi, xi - 1);
                            assert(best as int == if score_x >= prev { score_x } else { prev });
                            assert(best as int == Self::max_score(piles@, ii, mi, xi));
                            Self::lemma_max_score_bounds(piles@, ii, mi, xi);
                        }
                        x += 1;
                    }
                    proof {
                        let ghost ii = i as int;
                        let ghost mi = m as int;
                        assert(best as int == Self::max_score(piles@, ii, mi, 2 * mi));
                        assert(Self::optimal(piles@, ii, mi) == Self::max_score(piles@, ii, mi, 2 * mi));
                        Self::lemma_flat_idx_bound(ii, mi, ni);
                        assert(Self::flat(ii, mi, ni) == (i * stride + m) as int) by {
                            assert(stride as int == ni + 1);
                        }
                    }
                    let ghost old_dp = dp@;
                    dp.set(i * stride + m, best);
                    proof {
                        let ghost ii = i as int;
                        let ghost mi = m as int;
                        let ghost idx = Self::flat(ii, mi, ni);
                        assert(idx == (i * stride + m) as int) by {
                            assert(stride as int == ni + 1);
                        }
                        assert(dp@[idx] as int == Self::optimal(piles@, ii, mi));
                        assert forall |j: int, mm: int|
                            (ii + 1) <= j <= ni && 1 <= mm <= ni
                            implies dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm)
                        by {
                            Self::lemma_flat_idx_bound(j, mm, ni);
                            Self::lemma_flat_idx_ne_higher_row(ii, mi, j, mm, ni);
                            assert(Self::flat(j, mm, ni) != idx);
                            assert(dp@[Self::flat(j, mm, ni)] == old_dp[Self::flat(j, mm, ni)]);
                        }
                        assert forall |mm: int|
                            1 <= mm < mi
                            implies dp@[Self::flat(ii, mm, ni)] as int == Self::optimal(piles@, ii, mm)
                        by {
                            Self::lemma_flat_idx_bound(ii, mm, ni);
                            Self::lemma_flat_idx_ne_same_row(ii, mm, mi, ni);
                            assert(Self::flat(ii, mm, ni) != idx);
                            assert(dp@[Self::flat(ii, mm, ni)] == old_dp[Self::flat(ii, mm, ni)]);
                        }
                    }
                }
                m += 1;
            }

            
            proof {
                let ghost ii = i as int;
                assert forall |j: int, mm: int|
                    ii <= j <= ni && 1 <= mm <= ni
                    implies dp@[Self::flat(j, mm, ni)] as int == Self::optimal(piles@, j, mm)
                by {
                    Self::lemma_flat_idx_bound(j, mm, ni);
                    if j > ii {
                        assert((ii + 1) <= j);
                    } else {
                        assert(j == ii);
                        assert(1 <= mm);
                        assert(mm <= ni);
                    }
                }
            }
        }
        proof {
            assert(i == 0);
            assert(ni >= 1);
            Self::lemma_flat_idx_bound(0, 1, ni);
            assert(Self::flat(0, 1, ni) == 1int);
            assert(dp@[1] as int == Self::optimal(piles@, 0, 1));
        }
        dp[1]
    }
}

}
