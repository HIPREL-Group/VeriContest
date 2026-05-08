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
    }
}

}
