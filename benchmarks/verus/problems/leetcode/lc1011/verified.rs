use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_prefix(weights: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::sum_prefix(weights, n - 1) + weights[n - 1] as int
        }
    }

    pub open spec fn sum_weights(weights: Seq<i32>) -> int {
        Self::sum_prefix(weights, weights.len() as int)
    }

    pub open spec fn max_prefix(weights: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 1 {
            weights[0] as int
        } else {
            let prev = Self::max_prefix(weights, n - 1);
            let cur = weights[n - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn max_weight(weights: Seq<i32>) -> int {
        Self::max_prefix(weights, weights.len() as int)
    }

    pub open spec fn days_needed_rec(weights: Seq<i32>, cap: int, i: int, cur: int, used: int) -> int
        decreases weights.len() as int - i
    {
        if i >= weights.len() {
            used
        } else {
            let w = weights[i] as int;
            if cur + w <= cap {
                Self::days_needed_rec(weights, cap, i + 1, cur + w, used)
            } else {
                Self::days_needed_rec(weights, cap, i + 1, w, used + 1)
            }
        }
    }

    pub open spec fn days_needed(weights: Seq<i32>, cap: int) -> int {
        Self::days_needed_rec(weights, cap, 0, 0, 1)
    }

    proof fn lemma_max_prefix_upper(weights: Seq<i32>, n: int, i: int)
        requires
            1 <= n <= weights.len(),
            0 <= i < n,
        ensures
            weights[i] as int <= Self::max_prefix(weights, n),
        decreases n,
    {
        if n == 1 {
        } else {
            if i == n - 1 {
            } else {
                Self::lemma_max_prefix_upper(weights, n - 1, i);
            }
        }
    }

    proof fn lemma_max_prefix_is_elem(weights: Seq<i32>, n: int)
        requires
            1 <= n <= weights.len(),
        ensures
            exists |i: int| 0 <= i < n && weights[i] as int == Self::max_prefix(weights, n),
        decreases n,
    {
        if n == 1 {
            assert(Self::max_prefix(weights, n) == weights[0] as int);
            assert(0 <= 0 < n && weights[0] as int == Self::max_prefix(weights, n));
            assert(exists |i: int| 0 <= i < n && weights[i] as int == Self::max_prefix(weights, n));
        } else {
            Self::lemma_max_prefix_is_elem(weights, n - 1);
            let prev = Self::max_prefix(weights, n - 1);
            let cur = weights[n - 1] as int;
            if prev >= cur {
                let i = choose |i: int| 0 <= i < n - 1 && weights[i] as int == prev;
                assert(0 <= i < n && weights[i] as int == Self::max_prefix(weights, n));
                assert(exists |i: int| 0 <= i < n && weights[i] as int == Self::max_prefix(weights, n));
            } else {
                assert(0 <= n - 1 < n && weights[n - 1] as int == Self::max_prefix(weights, n));
                assert(exists |i: int| 0 <= i < n && weights[i] as int == Self::max_prefix(weights, n));
            }
        }
    }

    proof fn lemma_sum_prefix_upper(weights: Seq<i32>, n: int)
        requires
            0 <= n <= weights.len(),
            forall |i: int| 0 <= i < weights.len() ==> 1 <= #[trigger] weights[i],
        ensures
            Self::sum_prefix(weights, n) <= Self::sum_weights(weights),
        decreases weights.len() as int - n,
    {
        if n < weights.len() {
            Self::lemma_sum_prefix_upper(weights, n + 1);
            assert(Self::sum_prefix(weights, n + 1) <= Self::sum_weights(weights));
            assert(Self::sum_prefix(weights, n) <= Self::sum_prefix(weights, n + 1));
        }
    }

    proof fn lemma_days_needed_total_rec(weights: Seq<i32>, i: int)
        requires
            0 <= i <= weights.len(),
            forall |k: int| 0 <= k < weights.len() ==> 1 <= #[trigger] weights[k],
        ensures
            Self::days_needed_rec(
                weights,
                Self::sum_weights(weights),
                i,
                Self::sum_prefix(weights, i),
                1,
            ) == 1,
        decreases weights.len() as int - i,
    {
        if i < weights.len() {
            Self::lemma_sum_prefix_upper(weights, i + 1);
            assert(Self::sum_prefix(weights, i + 1) <= Self::sum_weights(weights));
            assert(Self::days_needed_rec(
                weights,
                Self::sum_weights(weights),
                i,
                Self::sum_prefix(weights, i),
                1,
            )
                == Self::days_needed_rec(
                    weights,
                    Self::sum_weights(weights),
                    i + 1,
                    Self::sum_prefix(weights, i + 1),
                    1,
                ));
            Self::lemma_days_needed_total_rec(weights, i + 1);
        }
    }

    proof fn lemma_days_needed_total(weights: Seq<i32>)
        requires
            weights.len() >= 1,
            forall |k: int| 0 <= k < weights.len() ==> 1 <= #[trigger] weights[k],
        ensures
            Self::days_needed(weights, Self::sum_weights(weights)) == 1,
    {
        Self::lemma_days_needed_total_rec(weights, 0);
    }

    pub fn ship_within_days(weights: Vec<i32>, days: i32) -> (res: i32)
        requires
            1 <= days <= weights.len() <= 50_000,
            forall |i: int| 0 <= i < weights.len() ==> 1 <= #[trigger] weights[i] <= 500,
        ensures
            Self::max_weight(weights@) <= res as int <= Self::sum_weights(weights@),
            Self::days_needed(weights@, res as int) <= days as int,
            res as int == Self::max_weight(weights@)
                || Self::days_needed(weights@, res as int - 1) > days as int,
    {
        let mut max_w = weights[0];
        let mut sum_w = weights[0];
        let mut i = 1usize;
        proof {
            assert(Self::sum_prefix(weights@, i as int) == Self::sum_prefix(weights@, 1));
            assert(Self::sum_prefix(weights@, 1) == Self::sum_prefix(weights@, 0) + weights[0] as int);
            assert(Self::sum_prefix(weights@, 0) == 0);
            assert(sum_w as int == Self::sum_prefix(weights@, i as int));
            assert(exists |k: int| 0 <= k < i as int && max_w == weights[k]);
        }
        while i < weights.len()
            invariant
                1 <= days <= weights.len() <= 50_000,
                forall |k: int| 0 <= k < weights.len() ==> 1 <= #[trigger] weights[k] <= 500,
                1 <= i <= weights.len(),
                1 <= max_w <= 500,
                0 <= sum_w <= 25_000_000,
                max_w <= sum_w,
                sum_w as int <= i as int * 500,
                sum_w as int == Self::sum_prefix(weights@, i as int),
                forall |k: int| 0 <= k < i as int ==> weights[k] <= max_w,
                exists |k: int| 0 <= k < i as int && max_w == weights[k],
            decreases weights.len() - i,
        {
            proof {
                assert(sum_w as int + weights[i as int] as int <= 25_000_000) by (nonlinear_arith)
                    requires
                        i < weights.len(),
                        weights.len() <= 50_000,
                        0 <= sum_w,
                        sum_w as int <= i as int * 500,
                        1 <= weights[i as int] as int <= 500,
                {
                }
            }
            if weights[i] > max_w {
                max_w = weights[i];
            }
            sum_w += weights[i];
            proof {
                assert(max_w <= sum_w);
            }
            i += 1;
        }

        proof {
            assert(max_w == Self::max_weight(weights@)) by {
                assert(max_w <= Self::max_weight(weights@)) by {
                    let k = choose |k: int| 0 <= k < weights.len() && max_w == weights[k];
                    Self::lemma_max_prefix_upper(weights@, weights.len() as int, k);
                }
                assert(Self::max_weight(weights@) <= max_w) by {
                    let m = Self::max_weight(weights@);
                    Self::lemma_max_prefix_is_elem(weights@, weights.len() as int);
                    assert(exists |k: int| 0 <= k < weights.len() && weights[k] as int == m);
                    let k = choose |k: int| 0 <= k < weights.len() && weights[k] as int == m;
                    assert(weights[k] <= max_w);
                }
            }
            assert(sum_w as int == Self::sum_weights(weights@));
            Self::lemma_days_needed_total(weights@);
        }

        let mut low = max_w;
        let mut high = sum_w;

        while low < high
            invariant
                1 <= days <= weights.len() <= 50_000,
                forall |k: int| 0 <= k < weights.len() ==> 1 <= #[trigger] weights[k] <= 500,
                max_w == Self::max_weight(weights@),
                sum_w as int == Self::sum_weights(weights@),
                1 <= max_w <= 500,
                0 <= sum_w <= 25_000_000,
                forall |k: int| 0 <= k < weights.len() ==> weights[k] <= max_w,
                max_w <= low <= high <= sum_w,
                Self::days_needed(weights@, high as int) <= days as int,
                low == max_w || Self::days_needed(weights@, low as int - 1) > days as int,
            decreases high - low,
        {
            let mid = low + (high - low) / 2;
            let mut need = 1;
            let mut cur = 0;
            let mut j = 0usize;
            while j < weights.len()
                invariant
                    1 <= days <= weights.len() <= 50_000,
                    forall |k: int| 0 <= k < weights.len() ==> 1 <= #[trigger] weights[k] <= 500,
                    max_w <= low <= mid <= high <= sum_w,
                    0 <= sum_w <= 25_000_000,
                    forall |k: int| 0 <= k < weights.len() ==> weights[k] <= max_w,
                    0 <= j <= weights.len(),
                    1 <= need <= j as int + 1,
                    0 <= cur <= mid,
                    Self::days_needed(weights@, mid as int)
                        == Self::days_needed_rec(weights@, mid as int, j as int, cur as int, need as int),
                decreases weights.len() - j,
            {
                proof {
                    assert(cur as int + weights[j as int] as int <= 25_000_500) by (nonlinear_arith)
                        requires
                            j < weights.len(),
                            0 <= cur <= mid,
                            mid <= sum_w,
                            0 <= sum_w <= 25_000_000,
                            1 <= weights[j as int] as int <= 500,
                    {
                    }
                }
                if cur + weights[j] > mid {
                    proof {
                        assert(Self::days_needed_rec(weights@, mid as int, j as int, cur as int, need as int)
                            == Self::days_needed_rec(
                                weights@,
                                mid as int,
                                j as int + 1,
                                weights[j as int] as int,
                                need as int + 1,
                            ));
                    }
                    need += 1;
                    cur = weights[j];
                } else {
                    proof {
                        assert(Self::days_needed_rec(weights@, mid as int, j as int, cur as int, need as int)
                            == Self::days_needed_rec(
                                weights@,
                                mid as int,
                                j as int + 1,
                                cur as int + weights[j as int] as int,
                                need as int,
                            ));
                    }
                    cur += weights[j];
                }
                j += 1;
            }

            proof {
                assert(Self::days_needed(weights@, mid as int) == need as int);
            }

            if need <= days {
                high = mid;
            } else {
                proof {
                    assert(Self::days_needed(weights@, mid as int) > days as int);
                }
                low = mid + 1;
            }

            proof {
                if need <= days {
                    assert(Self::days_needed(weights@, high as int) <= days as int);
                } else {
                    assert(low != max_w);
                    assert(Self::days_needed(weights@, low as int - 1) > days as int);
                }
            }
        }

        proof {
            assert(low == high);
            assert(Self::days_needed(weights@, low as int) <= days as int);
        }

        low
    }
}

}
