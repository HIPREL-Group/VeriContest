use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_segment(matrix: Seq<Vec<i32>>, row: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= row < matrix.len(),
            0 <= left <= right <= matrix[row].len(),
    {
        Seq::new((right - left) as nat, |i: int| matrix[row][left + i])
    }

    pub open spec fn col_segment(matrix: Seq<Vec<i32>>, col: int, top: int, bottom: int) -> Seq<i32>
        recommends
            0 <= top <= bottom <= matrix.len(),
            forall |r: int| 0 <= r < matrix.len() ==> col < #[trigger] matrix[r].len(),
    {
        Seq::new((bottom - top) as nat, |i: int| matrix[top + i][col])
    }

    pub open spec fn rev_row_segment(matrix: Seq<Vec<i32>>, row: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= row < matrix.len(),
            0 <= left <= right <= matrix[row].len(),
    {
        Seq::new((right - left) as nat, |i: int| matrix[row][right - 1 - i])
    }

    pub open spec fn rev_col_segment(matrix: Seq<Vec<i32>>, col: int, top: int, bottom: int) -> Seq<i32>
        recommends
            0 <= top <= bottom <= matrix.len(),
            forall |r: int| 0 <= r < matrix.len() ==> col < #[trigger] matrix[r].len(),
    {
        Seq::new((bottom - top) as nat, |i: int| matrix[bottom - 1 - i][col])
    }

    pub open spec fn layer_seq(matrix: Seq<Vec<i32>>, top: int, bottom: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= top < bottom <= matrix.len(),
            0 <= left < right,
            forall |r: int| 0 <= r < matrix.len() ==> right <= #[trigger] matrix[r].len(),
    {
        Self::row_segment(matrix, top, left, right)
        + Self::col_segment(matrix, right - 1, top + 1, bottom)
        + if top + 1 < bottom {
            Self::rev_row_segment(matrix, bottom - 1, left, right - 1)
        } else {
            seq![]
        }
        + if top + 1 < bottom && left + 1 < right {
            Self::rev_col_segment(matrix, left, top + 1, bottom - 1)
        } else {
            seq![]
        }
    }

    pub open spec fn spiral_region(matrix: Seq<Vec<i32>>, top: int, bottom: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= top <= bottom <= matrix.len(),
            0 <= left <= right,
            forall |r: int| 0 <= r < matrix.len() ==> right <= #[trigger] matrix[r].len(),
        decreases
            if top >= bottom || left >= right {
                0nat
            } else {
                (bottom - top + right - left) as nat
            },
    {
        if top >= bottom || left >= right {
            seq![]
        } else {
            Self::layer_seq(matrix, top, bottom, left, right)
            + if top + 1 < bottom && left + 1 < right {
                Self::spiral_region(matrix, top + 1, bottom - 1, left + 1, right - 1)
            } else {
                seq![]
            }
        }
    }

    pub fn spiral_order(matrix: Vec<Vec<i32>>) -> (res: Vec<i32>)
        requires
            1 <= matrix.len() <= 10,
            1 <= matrix[0].len() <= 10,
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==> -100 <= #[trigger] matrix[r][c] <= 100,
        ensures
            res@ == Self::spiral_region(matrix@, 0, matrix.len() as int, 0, matrix[0].len() as int),
    {
    }
}

}
