use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_inc(indices: Seq<Seq<i32>>, row: int, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::row_inc(indices, row, k - 1)
                + if indices[k - 1][0] as int == row { 1int } else { 0int }
        }
    }

    pub open spec fn col_inc(indices: Seq<Seq<i32>>, col: int, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::col_inc(indices, col, k - 1)
                + if indices[k - 1][1] as int == col { 1int } else { 0int }
        }
    }

    pub open spec fn cell_val(indices: Seq<Seq<i32>>, row: int, col: int) -> int {
        Self::row_inc(indices, row, indices.len() as int)
            + Self::col_inc(indices, col, indices.len() as int)
    }

    pub open spec fn count_odd_in_row(indices: Seq<Seq<i32>>, row: int, j: int) -> int
        decreases j,
    {
        if j <= 0 {
            0
        } else {
            Self::count_odd_in_row(indices, row, j - 1)
                + if Self::cell_val(indices, row, j - 1) % 2 != 0 { 1int } else { 0int }
        }
    }

    pub open spec fn count_odd(indices: Seq<Seq<i32>>, n: int, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            Self::count_odd(indices, n, i - 1) + Self::count_odd_in_row(indices, i - 1, n)
        }
    }

    pub open spec fn spec_count_odd_rows(indices: Seq<Seq<i32>>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            Self::spec_count_odd_rows(indices, i - 1)
                + if Self::row_inc(indices, i - 1, indices.len() as int) % 2 != 0 { 1int } else { 0int }
        }
    }

    pub open spec fn spec_count_odd_cols(indices: Seq<Seq<i32>>, j: int) -> int
        decreases j,
    {
        if j <= 0 {
            0
        } else {
            Self::spec_count_odd_cols(indices, j - 1)
                + if Self::col_inc(indices, j - 1, indices.len() as int) % 2 != 0 { 1int } else { 0int }
        }
    }

    proof fn lemma_count_odd_in_row_bounds(indices: Seq<Seq<i32>>, row: int, j: int)
        requires
            0 <= j,
        ensures
            0 <= Self::count_odd_in_row(indices, row, j) <= j,
        decreases j,
    {
        if j > 0 {
            Self::lemma_count_odd_in_row_bounds(indices, row, j - 1);
        }
    }

    proof fn lemma_count_odd_bounds(indices: Seq<Seq<i32>>, n: int, i: int)
        requires
            0 <= i,
            0 <= n,
        ensures
            0 <= Self::count_odd(indices, n, i) <= i * n,
        decreases i,
    {
        if i > 0 {
            Self::lemma_count_odd_bounds(indices, n, i - 1);
            Self::lemma_count_odd_in_row_bounds(indices, i - 1, n);
            assert(Self::count_odd(indices, n, i) <= i * n) by(nonlinear_arith)
                requires
                    Self::count_odd(indices, n, i)
                        == Self::count_odd(indices, n, i - 1)
                            + Self::count_odd_in_row(indices, i - 1, n),
                    Self::count_odd(indices, n, i - 1) <= (i - 1) * n,
                    Self::count_odd_in_row(indices, i - 1, n) <= n,
            ;
        }
    }

    proof fn lemma_spec_count_odd_rows_bounds(indices: Seq<Seq<i32>>, i: int)
        requires
            0 <= i,
        ensures
            0 <= Self::spec_count_odd_rows(indices, i) <= i,
        decreases i,
    {
        if i > 0 {
            Self::lemma_spec_count_odd_rows_bounds(indices, i - 1);
        }
    }

    proof fn lemma_spec_count_odd_cols_bounds(indices: Seq<Seq<i32>>, j: int)
        requires
            0 <= j,
        ensures
            0 <= Self::spec_count_odd_cols(indices, j) <= j,
        decreases j,
    {
        if j > 0 {
            Self::lemma_spec_count_odd_cols_bounds(indices, j - 1);
        }
    }

    proof fn lemma_count_odd_in_row_split(indices: Seq<Seq<i32>>, r: int, j: int)
        requires
            0 <= j,
        ensures
            Self::row_inc(indices, r, indices.len() as int) % 2 != 0 ==>
                Self::count_odd_in_row(indices, r, j) == j - Self::spec_count_odd_cols(indices, j),
            Self::row_inc(indices, r, indices.len() as int) % 2 == 0 ==>
                Self::count_odd_in_row(indices, r, j) == Self::spec_count_odd_cols(indices, j),
        decreases j,
    {
        if j > 0 {
            Self::lemma_count_odd_in_row_split(indices, r, j - 1);
            let ri = Self::row_inc(indices, r, indices.len() as int);
            let ci = Self::col_inc(indices, j - 1, indices.len() as int);
            assert((ri + ci) % 2 != 0 <==> ri % 2 != ci % 2) by(nonlinear_arith);
        }
    }

    proof fn lemma_count_odd_formula(indices: Seq<Seq<i32>>, n: int, i: int)
        requires
            0 <= i,
            0 <= n,
        ensures
            Self::count_odd(indices, n, i) ==
                Self::spec_count_odd_rows(indices, i) * (n - Self::spec_count_odd_cols(indices, n))
                + (i - Self::spec_count_odd_rows(indices, i)) * Self::spec_count_odd_cols(indices, n),
        decreases i,
    {
        let oc = Self::spec_count_odd_cols(indices, n);
        if i <= 0 {
            assert(Self::count_odd(indices, n, i) == 0);
            assert(Self::spec_count_odd_rows(indices, i) == 0);
            assert(0int * (n - oc) + (i - 0int) * oc == i * oc) by(nonlinear_arith);
            assert(i * oc == 0) by(nonlinear_arith)
                requires i == 0;
        } else {
            Self::lemma_count_odd_formula(indices, n, i - 1);
            Self::lemma_count_odd_in_row_split(indices, i - 1, n);

            let or_prev = Self::spec_count_odd_rows(indices, i - 1);
            let or_curr = Self::spec_count_odd_rows(indices, i);
            let coir = Self::count_odd_in_row(indices, i - 1, n);
            let co_prev = Self::count_odd(indices, n, i - 1);

            assert(Self::count_odd(indices, n, i) == co_prev + coir);
            assert(co_prev == or_prev * (n - oc) + (i - 1 - or_prev) * oc);

            if Self::row_inc(indices, i - 1, indices.len() as int) % 2 != 0 {
                assert(or_curr == or_prev + 1);
                assert(coir == n - oc);
                assert(or_curr * (n - oc) + (i - or_curr) * oc
                    == co_prev + coir) by(nonlinear_arith)
                    requires
                        co_prev == or_prev * (n - oc) + (i - 1 - or_prev) * oc,
                        coir == n - oc,
                        or_curr == or_prev + 1;
            } else {
                assert(or_curr == or_prev);
                assert(coir == oc);
                assert(or_curr * (n - oc) + (i - or_curr) * oc
                    == co_prev + coir) by(nonlinear_arith)
                    requires
                        co_prev == or_prev * (n - oc) + (i - 1 - or_prev) * oc,
                        coir == oc,
                        or_curr == or_prev;
            }

            assert(Self::count_odd(indices, n, i)
                == or_curr * (n - oc) + (i - or_curr) * oc);
        }
    }

    pub fn odd_cells(m: i32, n: i32, indices: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= m <= 50,
            1 <= n <= 50,
            1 <= indices.len() <= 100,
            forall|k: int|
                0 <= k < indices.len() ==> (#[trigger] indices.deep_view()[k]).len() == 2,
            forall|k: int|
                0 <= k < indices.len() ==> 0 <= (#[trigger] indices.deep_view()[k])[0] < m,
            forall|k: int|
                0 <= k < indices.len() ==> 0 <= (#[trigger] indices.deep_view()[k])[1] < n,
        ensures
            result as int == Self::count_odd(indices.deep_view(), n as int, m as int),
    {
        let ghost idx_seq = indices.deep_view();

        let mut row_counts: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < m as usize
            invariant
                row_counts.len() == idx,
                idx <= m as usize,
                1 <= m <= 50,
                forall|r: int| 0 <= r < idx as int ==> row_counts@[r] == 0i32,
            decreases m as usize - idx,
        {
            row_counts.push(0);
            idx = idx + 1;
        }

        let mut col_counts: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n as usize
            invariant
                col_counts.len() == idx,
                idx <= n as usize,
                1 <= n <= 50,
                forall|c: int| 0 <= c < idx as int ==> col_counts@[c] == 0i32,
            decreases n as usize - idx,
        {
            col_counts.push(0);
            idx = idx + 1;
        }

        let mut k: usize = 0;
        while k < indices.len()
            invariant
                k <= indices.len(),
                row_counts.len() == m as usize,
                col_counts.len() == n as usize,
                idx_seq == indices.deep_view(),
                1 <= m <= 50,
                1 <= n <= 50,
                indices.len() <= 100,
                forall|r: int| 0 <= r < m as int ==>
                    (#[trigger] row_counts@[r]) as int == Self::row_inc(idx_seq, r, k as int),
                forall|c: int| 0 <= c < n as int ==>
                    (#[trigger] col_counts@[c]) as int == Self::col_inc(idx_seq, c, k as int),
                forall|r: int| 0 <= r < m as int ==>
                    0 <= (#[trigger] row_counts@[r]) as int <= k as int,
                forall|c: int| 0 <= c < n as int ==>
                    0 <= (#[trigger] col_counts@[c]) as int <= k as int,
                forall|p: int|
                    0 <= p < indices.len() ==> (#[trigger] idx_seq[p]).len() == 2,
                forall|p: int|
                    0 <= p < indices.len() ==> 0 <= (#[trigger] idx_seq[p])[0] < m,
                forall|p: int|
                    0 <= p < indices.len() ==> 0 <= (#[trigger] idx_seq[p])[1] < n,
            decreases indices.len() - k,
        {
            proof {
                assert(idx_seq[k as int] =~= indices@[k as int]@);
                assert(indices@[k as int]@.len() == 2);
            }

            let r_val: i32 = indices[k][0];
            let c_val: i32 = indices[k][1];

            proof {
                assert(0 <= r_val < m);
                assert(0 <= c_val < n);
            }

            let r: usize = r_val as usize;
            let c: usize = c_val as usize;

            let ghost pre_row = row_counts@;
            let ghost pre_col = col_counts@;

            let old_r = row_counts[r];
            row_counts.set(r, old_r + 1);
            let old_c = col_counts[c];
            col_counts.set(c, old_c + 1);

            proof {
                assert(r_val as int == idx_seq[k as int][0] as int);
                assert(c_val as int == idx_seq[k as int][1] as int);

                assert forall|r_idx: int| 0 <= r_idx < m as int implies
                    (#[trigger] row_counts@[r_idx]) as int
                        == Self::row_inc(idx_seq, r_idx, k as int + 1)
                by {
                    if r_idx == r_val as int {
                        assert(row_counts@[r_idx] == old_r + 1);
                    } else {
                        assert(row_counts@[r_idx] == pre_row[r_idx]);
                    }
                };

                assert forall|c_idx: int| 0 <= c_idx < n as int implies
                    (#[trigger] col_counts@[c_idx]) as int
                        == Self::col_inc(idx_seq, c_idx, k as int + 1)
                by {
                    if c_idx == c_val as int {
                        assert(col_counts@[c_idx] == old_c + 1);
                    } else {
                        assert(col_counts@[c_idx] == pre_col[c_idx]);
                    }
                };

                assert forall|r_idx: int| 0 <= r_idx < m as int implies
                    0 <= (#[trigger] row_counts@[r_idx]) as int <= k as int + 1
                by {
                    if r_idx == r_val as int {
                        assert(row_counts@[r_idx] == old_r + 1);
                        assert(old_r as int <= k as int);
                    } else {
                        assert(row_counts@[r_idx] == pre_row[r_idx]);
                        assert(pre_row[r_idx] as int <= k as int);
                    }
                };

                assert forall|c_idx: int| 0 <= c_idx < n as int implies
                    0 <= (#[trigger] col_counts@[c_idx]) as int <= k as int + 1
                by {
                    if c_idx == c_val as int {
                        assert(col_counts@[c_idx] == old_c + 1);
                        assert(old_c as int <= k as int);
                    } else {
                        assert(col_counts@[c_idx] == pre_col[c_idx]);
                        assert(pre_col[c_idx] as int <= k as int);
                    }
                };
            }

            k = k + 1;
        }

        let mut odd_rows: i32 = 0;
        let mut i: usize = 0;

        while i < m as usize
            invariant
                i <= m as usize,
                row_counts.len() == m as usize,
                col_counts.len() == n as usize,
                idx_seq == indices.deep_view(),
                1 <= m <= 50,
                1 <= n <= 50,
                odd_rows as int == Self::spec_count_odd_rows(idx_seq, i as int),
                0 <= odd_rows <= i as i32,
                forall|r: int| 0 <= r < m as int ==>
                    (#[trigger] row_counts@[r]) as int
                        == Self::row_inc(idx_seq, r, indices.len() as int),
                forall|c: int| 0 <= c < n as int ==>
                    (#[trigger] col_counts@[c]) as int
                        == Self::col_inc(idx_seq, c, indices.len() as int),
                forall|r: int| 0 <= r < m as int ==>
                    0 <= (#[trigger] row_counts@[r]) <= 100,
                forall|c: int| 0 <= c < n as int ==>
                    0 <= (#[trigger] col_counts@[c]) <= 100,
            decreases m as usize - i,
        {
            proof {
                let ri = Self::row_inc(idx_seq, i as int, idx_seq.len() as int);
                assert(row_counts@[i as int] as int == ri);
                assert(0 <= row_counts@[i as int]);
                assert((row_counts@[i as int] % 2 != 0) == (ri % 2 != 0)) by {
                    assert(row_counts@[i as int] as int == ri);
                };
            }
            if row_counts[i] % 2 != 0 {
                odd_rows = odd_rows + 1;
            }
            i = i + 1;
        }

        let mut odd_cols: i32 = 0;
        let mut j: usize = 0;

        while j < n as usize
            invariant
                j <= n as usize,
                row_counts.len() == m as usize,
                col_counts.len() == n as usize,
                idx_seq == indices.deep_view(),
                1 <= m <= 50,
                1 <= n <= 50,
                odd_cols as int == Self::spec_count_odd_cols(idx_seq, j as int),
                0 <= odd_cols <= j as i32,
                odd_rows as int == Self::spec_count_odd_rows(idx_seq, m as int),
                0 <= odd_rows <= m,
                forall|r: int| 0 <= r < m as int ==>
                    (#[trigger] row_counts@[r]) as int
                        == Self::row_inc(idx_seq, r, indices.len() as int),
                forall|c: int| 0 <= c < n as int ==>
                    (#[trigger] col_counts@[c]) as int
                        == Self::col_inc(idx_seq, c, indices.len() as int),
                forall|r: int| 0 <= r < m as int ==>
                    0 <= (#[trigger] row_counts@[r]) <= 100,
                forall|c: int| 0 <= c < n as int ==>
                    0 <= (#[trigger] col_counts@[c]) <= 100,
            decreases n as usize - j,
        {
            proof {
                let ci = Self::col_inc(idx_seq, j as int, idx_seq.len() as int);
                assert(col_counts@[j as int] as int == ci);
                assert(0 <= col_counts@[j as int]);
                assert((col_counts@[j as int] % 2 != 0) == (ci % 2 != 0)) by {
                    assert(col_counts@[j as int] as int == ci);
                };
            }
            if col_counts[j] % 2 != 0 {
                odd_cols = odd_cols + 1;
            }
            j = j + 1;
        }

        proof {
            Self::lemma_count_odd_formula(idx_seq, n as int, m as int);
            Self::lemma_spec_count_odd_rows_bounds(idx_seq, m as int);
            Self::lemma_spec_count_odd_cols_bounds(idx_seq, n as int);
            Self::lemma_count_odd_bounds(idx_seq, n as int, m as int);

            assert(odd_rows as int == Self::spec_count_odd_rows(idx_seq, m as int));
            assert(odd_cols as int == Self::spec_count_odd_cols(idx_seq, n as int));

            assert(0 <= odd_rows <= 50);
            assert(0 <= odd_cols <= 50);
            assert(0 <= n - odd_cols <= 50);
            assert(0 <= m - odd_rows <= 50);

            assert(0 <= odd_rows as int * (n as int - odd_cols as int) <= 2500) by(nonlinear_arith)
                requires 0 <= odd_rows <= 50, 0 <= n - odd_cols <= 50;
            assert(0 <= odd_cols as int * (m as int - odd_rows as int) <= 2500) by(nonlinear_arith)
                requires 0 <= odd_cols <= 50, 0 <= m - odd_rows <= 50;
        }

        odd_rows * (n - odd_cols) + odd_cols * (m - odd_rows)
    }
}

}
