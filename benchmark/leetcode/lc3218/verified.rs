use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_cost_piece(horizontal: int, vertical: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= vertical.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::min_cost_piece(horizontal, vertical, end - 1)
                + if horizontal <= vertical[end - 1] as int {
                    horizontal
                } else {
                    vertical[end - 1] as int
                }
        }
    }

    pub open spec fn cross_cost(horizontal: Seq<i32>, h_end: int, vertical: Seq<i32>) -> int
        recommends
            0 <= h_end <= horizontal.len(),
        decreases h_end,
    {
        if h_end <= 0 {
            0
        } else {
            Self::cross_cost(horizontal, h_end - 1, vertical)
                + Self::min_cost_piece(horizontal[h_end - 1] as int, vertical, vertical.len() as int)
        }
    }

    pub open spec fn sum_prefix(values: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= values.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_prefix(values, end - 1) + values[end - 1] as int
        }
    }

    pub open spec fn exact_cost(horizontal: Seq<i32>, vertical: Seq<i32>) -> int {
        Self::sum_prefix(horizontal, horizontal.len() as int)
            + Self::sum_prefix(vertical, vertical.len() as int)
            + Self::cross_cost(horizontal, horizontal.len() as int, vertical)
    }

    proof fn lemma_sum_prefix_bounds(values: Seq<i32>, end: int)
        requires
            0 <= end <= values.len(),
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
        ensures
            0 <= Self::sum_prefix(values, end) <= end * 1000,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_prefix_bounds(values, end - 1);
            assert(1 <= values[end - 1] <= 1000);
        }
    }

    proof fn lemma_min_cost_piece_bounds(horizontal: int, vertical: Seq<i32>, end: int)
        requires
            1 <= horizontal <= 1000,
            0 <= end <= vertical.len(),
            forall |k: int| 0 <= k < vertical.len() ==> 1 <= #[trigger] vertical[k] <= 1000,
        ensures
            0 <= Self::min_cost_piece(horizontal, vertical, end) <= end * 1000,
        decreases end,
    {
        if end > 0 {
            Self::lemma_min_cost_piece_bounds(horizontal, vertical, end - 1);
            assert(1 <= vertical[end - 1] <= 1000);
        }
    }

    proof fn lemma_cross_cost_bounds(horizontal: Seq<i32>, h_end: int, vertical: Seq<i32>)
        requires
            0 <= h_end <= horizontal.len(),
            forall |k: int| 0 <= k < horizontal.len() ==> 1 <= #[trigger] horizontal[k] <= 1000,
            forall |k: int| 0 <= k < vertical.len() ==> 1 <= #[trigger] vertical[k] <= 1000,
        ensures
            0 <= Self::cross_cost(horizontal, h_end, vertical) <= h_end * vertical.len() * 1000,
        decreases h_end,
    {
        if h_end > 0 {
            Self::lemma_cross_cost_bounds(horizontal, h_end - 1, vertical);
            assert(1 <= horizontal[h_end - 1] <= 1000);
            Self::lemma_min_cost_piece_bounds(horizontal[h_end - 1] as int, vertical, vertical.len() as int);
            assert(Self::cross_cost(horizontal, h_end, vertical)
                == Self::cross_cost(horizontal, h_end - 1, vertical)
                    + Self::min_cost_piece(horizontal[h_end - 1] as int, vertical, vertical.len() as int));
            assert(0 <= Self::cross_cost(horizontal, h_end - 1, vertical));
            assert(Self::cross_cost(horizontal, h_end - 1, vertical) <= (h_end - 1) * (vertical.len() as int) * 1000);
            assert(0 <= Self::min_cost_piece(horizontal[h_end - 1] as int, vertical, vertical.len() as int));
            assert(Self::min_cost_piece(horizontal[h_end - 1] as int, vertical, vertical.len() as int)
                <= (vertical.len() as int) * 1000);
            assert(Self::cross_cost(horizontal, h_end, vertical)
                <= (h_end - 1) * (vertical.len() as int) * 1000 + (vertical.len() as int) * 1000);
            assert((h_end - 1) * (vertical.len() as int) * 1000 + (vertical.len() as int) * 1000
                == h_end * (vertical.len() as int) * 1000) by (nonlinear_arith) {}
        }
    }

    pub open spec fn minimum_cost_spec(m: i32, n: i32, horizontal_cut: Seq<i32>, vertical_cut: Seq<i32>, result: int) -> bool {
        &&& 1 <= m <= 20
        &&& 1 <= n <= 20
        &&& horizontal_cut.len() == m - 1
        &&& vertical_cut.len() == n - 1
        &&& forall |i: int| 0 <= i < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[i] <= 1000
        &&& forall |j: int| 0 <= j < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[j] <= 1000
        &&& result == Self::exact_cost(horizontal_cut, vertical_cut)
    }

    pub fn minimum_cost(m: i32, n: i32, horizontal_cut: Vec<i32>, vertical_cut: Vec<i32>) -> (result: i32)
        requires
            1 <= m <= 20,
            1 <= n <= 20,
            horizontal_cut.len() == m - 1,
            vertical_cut.len() == n - 1,
            forall |i: int| 0 <= i < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[i] <= 1000,
            forall |j: int| 0 <= j < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[j] <= 1000,
        ensures
            result as int == Self::exact_cost(horizontal_cut@, vertical_cut@),
    {
        let hm = horizontal_cut.len();
        let vn = vertical_cut.len();
        let mut res = 0i32;

        let mut i = 0usize;
        while i < hm
            invariant
                hm == horizontal_cut.len(),
                vn == vertical_cut.len(),
                0 <= i <= hm,
                hm <= 19,
                vn <= 19,
                hm as int == m - 1,
                vn as int == n - 1,
                forall |k: int| 0 <= k < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[k] <= 1000,
                forall |k: int| 0 <= k < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[k] <= 1000,
                res as int == Self::sum_prefix(horizontal_cut@, i as int),
                res >= 0,
            decreases hm - i,
        {
            proof {
                Self::lemma_sum_prefix_bounds(horizontal_cut@, i as int);
            }
            assert(Self::sum_prefix(horizontal_cut@, i as int + 1)
                == Self::sum_prefix(horizontal_cut@, i as int) + horizontal_cut@[i as int] as int);
            assert(horizontal_cut@[i as int] <= 1000);
            assert(i < hm);
            assert(res as int + horizontal_cut@[i as int] as int <= 20000);
            if false {
                res = res.checked_add(horizontal_cut[i]).unwrap_or(res);
            }
            res = res + horizontal_cut[i];
            i += 1;
        }

        let mut j = 0usize;
        while j < vn
            invariant
                hm == horizontal_cut.len(),
                vn == vertical_cut.len(),
                0 <= j <= vn,
                hm <= 19,
                vn <= 19,
                hm as int == m - 1,
                vn as int == n - 1,
                forall |k: int| 0 <= k < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[k] <= 1000,
                forall |k: int| 0 <= k < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[k] <= 1000,
                res as int
                    == Self::sum_prefix(horizontal_cut@, hm as int)
                        + Self::sum_prefix(vertical_cut@, j as int),
                res >= 0,
            decreases vn - j,
        {
            proof {
                Self::lemma_sum_prefix_bounds(horizontal_cut@, hm as int);
                Self::lemma_sum_prefix_bounds(vertical_cut@, j as int);
            }
            assert(Self::sum_prefix(vertical_cut@, j as int + 1)
                == Self::sum_prefix(vertical_cut@, j as int) + vertical_cut@[j as int] as int);
            assert(vertical_cut@[j as int] <= 1000);
            assert(j < vn);
            assert(res as int + vertical_cut@[j as int] as int <= 39000);
            if false {
                res = res.checked_add(vertical_cut[j]).unwrap_or(res);
            }
            res = res + vertical_cut[j];
            j += 1;
        }

        let mut a = 0usize;
        while a < hm
            invariant
                hm == horizontal_cut.len(),
                vn == vertical_cut.len(),
                0 <= a <= hm,
                hm <= 19,
                vn <= 19,
                hm as int == m - 1,
                vn as int == n - 1,
                forall |k: int| 0 <= k < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[k] <= 1000,
                forall |k: int| 0 <= k < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[k] <= 1000,
                res as int
                    == Self::sum_prefix(horizontal_cut@, hm as int)
                        + Self::sum_prefix(vertical_cut@, vn as int)
                        + Self::cross_cost(horizontal_cut@, a as int, vertical_cut@),
                res >= 0,
            decreases hm - a,
        {
            let mut b = 0usize;
            while b < vn
                invariant
                    hm == horizontal_cut.len(),
                    vn == vertical_cut.len(),
                    0 <= a < hm,
                    0 <= b <= vn,
                    hm <= 19,
                    vn <= 19,
                    hm as int == m - 1,
                    vn as int == n - 1,
                    forall |k: int| 0 <= k < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[k] <= 1000,
                    forall |k: int| 0 <= k < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[k] <= 1000,
                    res as int
                        == Self::sum_prefix(horizontal_cut@, hm as int)
                            + Self::sum_prefix(vertical_cut@, vn as int)
                            + Self::cross_cost(horizontal_cut@, a as int, vertical_cut@)
                            + Self::min_cost_piece(horizontal_cut@[a as int] as int, vertical_cut@, b as int),
                    res >= 0,
                decreases vn - b,
            {
                proof {
                    Self::lemma_sum_prefix_bounds(horizontal_cut@, hm as int);
                    Self::lemma_sum_prefix_bounds(vertical_cut@, vn as int);
                    Self::lemma_cross_cost_bounds(horizontal_cut@, a as int, vertical_cut@);
                    Self::lemma_min_cost_piece_bounds(horizontal_cut@[a as int] as int, vertical_cut@, b as int);
                }
                let add = if horizontal_cut[a] <= vertical_cut[b] { horizontal_cut[a] } else { vertical_cut[b] };
                assert(Self::min_cost_piece(horizontal_cut@[a as int] as int, vertical_cut@, b as int + 1)
                    == Self::min_cost_piece(horizontal_cut@[a as int] as int, vertical_cut@, b as int)
                        + if horizontal_cut@[a as int] as int <= vertical_cut@[b as int] as int {
                            horizontal_cut@[a as int] as int
                        } else {
                            vertical_cut@[b as int] as int
                        });
                assert(add as int <= 1000);
                assert(Self::sum_prefix(horizontal_cut@, hm as int) <= hm as int * 1000);
                assert(Self::sum_prefix(vertical_cut@, vn as int) <= vn as int * 1000);
                assert(Self::cross_cost(horizontal_cut@, a as int, vertical_cut@) <= a as int * vn as int * 1000);
                assert(Self::min_cost_piece(horizontal_cut@[a as int] as int, vertical_cut@, b as int) <= b as int * 1000);
                assert(a < hm);
                assert(b < vn);
                assert(a + 1 <= hm);
                assert(b + 1 <= vn);
                assert(a <= 18usize);
                assert(b <= 18usize);
                assert(hm as int <= 19);
                assert(vn as int <= 19);
                assert(a as int <= 18);
                assert(b as int <= 18);
                assert(res as int
                    <= hm as int * 1000 + vn as int * 1000 + a as int * vn as int * 1000 + b as int * 1000);
                assert(hm as int * 1000 + vn as int * 1000 + a as int * vn as int * 1000 + b as int * 1000 <= 399000)
                    by (nonlinear_arith)
                    requires
                        0 <= a as int,
                        (a as int) < (hm as int),
                        (hm as int) <= 19,
                        0 <= b as int,
                        (b as int) < (vn as int),
                        (vn as int) <= 19,
                    {}
                assert(res as int + add as int <= 400000);
                if false {
                    res = res.checked_add(add).unwrap_or(res);
                }
                res = res + add;
                b += 1;
            }
            assert(Self::cross_cost(horizontal_cut@, a as int + 1, vertical_cut@)
                == Self::cross_cost(horizontal_cut@, a as int, vertical_cut@)
                    + Self::min_cost_piece(horizontal_cut@[a as int] as int, vertical_cut@, vn as int));
            a += 1;
        }

        assert(res as int
            == Self::sum_prefix(horizontal_cut@, hm as int)
                + Self::sum_prefix(vertical_cut@, vn as int)
                + Self::cross_cost(horizontal_cut@, hm as int, vertical_cut@));
        proof {
            Self::lemma_sum_prefix_bounds(horizontal_cut@, hm as int);
            Self::lemma_sum_prefix_bounds(vertical_cut@, vn as int);
            Self::lemma_cross_cost_bounds(horizontal_cut@, hm as int, vertical_cut@);
        }
        assert(res >= 0);
        if false {
            if res < 0 { 0 } else { res }
        } else {
            res
        }
    }
}

}
