use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn total_diags(matrix: Seq<Vec<i32>>) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
    {
        matrix.len() + matrix[0].len() - 1
    }

    pub open spec fn diag_start_row(matrix: Seq<Vec<i32>>, d: int) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        if d < matrix[0].len() {
            0
        } else {
            d - (matrix[0].len() - 1)
        }
    }

    pub open spec fn diag_end_row(matrix: Seq<Vec<i32>>, d: int) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        if d < matrix.len() {
            d
        } else {
            matrix.len() - 1
        }
    }

    pub open spec fn diag_len(matrix: Seq<Vec<i32>>, d: int) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        Self::diag_end_row(matrix, d) - Self::diag_start_row(matrix, d) + 1
    }

    pub open spec fn diag_nth(matrix: Seq<Vec<i32>>, d: int, k: int) -> i32
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
            0 <= k < Self::diag_len(matrix, d),
    {
        let row = if d % 2 == 0 {
            Self::diag_end_row(matrix, d) - k
        } else {
            Self::diag_start_row(matrix, d) + k
        };
        matrix[row][d - row]
    }

    pub open spec fn diag_seq(matrix: Seq<Vec<i32>>, d: int) -> Seq<i32>
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        Seq::new(Self::diag_len(matrix, d) as nat, |k: int| Self::diag_nth(matrix, d, k))
    }

    pub open spec fn diagonal_prefix(matrix: Seq<Vec<i32>>, diag_count: int) -> Seq<i32>
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= diag_count <= Self::total_diags(matrix),
        decreases diag_count,
    {
        if diag_count <= 0 {
            seq![]
        } else {
            Self::diagonal_prefix(matrix, diag_count - 1) + Self::diag_seq(matrix, diag_count - 1)
        }
    }

    pub fn find_diagonal_order(mat: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= mat.len() <= 10_000,
            1 <= mat[0].len() <= 10_000,
            forall |r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == mat[0].len(),
            forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[0].len() ==> -100_000 <= #[trigger] mat[r][c] <= 100_000,
            mat.len() * mat[0].len() <= 10_000,
        ensures
            result@ == Self::diagonal_prefix(mat@, Self::total_diags(mat@)),
    {
        let rows = mat.len();
        let cols = mat[0].len();
        let total = rows + cols - 1;
        let mut result: Vec<i32> = Vec::new();
        let mut d: usize = 0;
        while d < total {
            let start = if d < cols { 0 } else { d - (cols - 1) };
            let end = if d < rows { d } else { rows - 1 };
            let len = end - start + 1;
            let mut k: usize = 0;
            while k < len {
                let row = if d % 2 == 0 { end - k } else { start + k };
                let col = d - row;
                let v = mat[row][col];
                result.push(v);
                k = k + 1;
            }
            d = d + 1;
        }
        result
    }
}

}
