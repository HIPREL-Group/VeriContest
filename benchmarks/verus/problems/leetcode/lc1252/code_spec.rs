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

        let mut row_counts: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < m as usize {
            row_counts.push(0);
            idx = idx + 1;
        }
        let mut col_counts: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n as usize {
            col_counts.push(0);
            idx = idx + 1;
        }
        let mut k: usize = 0;
        while k < indices.len() {
            let r_val: i32 = indices[k][0];
            let c_val: i32 = indices[k][1];
            let r: usize = r_val as usize;
            let c: usize = c_val as usize;
            let old_r = row_counts[r];
            row_counts.set(r, old_r + 1);
            let old_c = col_counts[c];
            col_counts.set(c, old_c + 1);
            k = k + 1;
        }
        let mut odd_rows: i32 = 0;
        let mut i: usize = 0;
        while i < m as usize {
            if row_counts[i] % 2 != 0 {
                odd_rows = odd_rows + 1;
            }
            i = i + 1;
        }
        let mut odd_cols: i32 = 0;
        let mut j: usize = 0;
        while j < n as usize {
            if col_counts[j] % 2 != 0 {
                odd_cols = odd_cols + 1;
            }
            j = j + 1;
        }
        odd_rows * (n - odd_cols) + odd_cols * (m - odd_rows)
    }
}

}
