use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn layer(n: int, row: int, col: int) -> int {
        Self::min2(
            Self::min2(row, col),
            Self::min2(n - 1 - row, n - 1 - col),
        )
    }

    pub open spec fn side_len(n: int, row: int, col: int) -> int {
        n - 2 * Self::layer(n, row, col)
    }

    pub open spec fn layer_start(n: int, row: int, col: int) -> int {
        1 + n * n - Self::side_len(n, row, col) * Self::side_len(n, row, col)
    }

    pub open spec fn spiral_value(n: int, row: int, col: int) -> int {
        let layer = Self::layer(n, row, col);
        let side = Self::side_len(n, row, col);
        let start = Self::layer_start(n, row, col);
        let last = n - 1 - layer;
        if side == 1 {
            start
        } else if row == layer {
            start + (col - layer)
        } else if col == last {
            start + (side - 1) + (row - layer)
        } else if row == last {
            start + 2 * (side - 1) + (last - col)
        } else {
            start + 3 * (side - 1) + (last - row)
        }
    }

    pub fn generate_matrix(n: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= n <= 20,
        ensures
            res.len() == n as int,
            forall |i: int| 0 <= i < n ==> #[trigger] res[i].len() == n as int,
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] res[i][j] as int == Self::spiral_value(n as int, i, j),
    {
    }
}

}
