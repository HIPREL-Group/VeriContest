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

    fn value_at(n: i32, row: i32, col: i32) -> (value: i32)
        requires
            1 <= n <= 20,
            0 <= row < n,
            0 <= col < n,
        ensures
            value as int == Self::spiral_value(n as int, row as int, col as int),
    {
        let a = if row <= col { row } else { col };
        let b_row = n - 1 - row;
        let b_col = n - 1 - col;
        let b = if b_row <= b_col { b_row } else { b_col };
        let layer = if a <= b { a } else { b };
        let side = n - 2 * layer;
        let start = 1 + (n * n - side * side);
        let last = n - 1 - layer;
        let value =
            if side == 1 {
                start
            } else {
                let offset =
                    if row == layer {
                        col - layer
                    } else if col == last {
                        (side - 1) + (row - layer)
                    } else if row == last {
                        2 * (side - 1) + (last - col)
                    } else {
                        3 * (side - 1) + (last - row)
                    };
                start + offset
            };
        value
    }

    pub fn generate_matrix(n: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= n <= 20,
        ensures
            res.len() == n as int,
            forall |i: int| 0 <= i < n ==> #[trigger] res[i].len() == n as int,
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] res[i][j] as int == Self::spiral_value(n as int, i, j),
    {
        let size = n as usize;
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < size {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < size {
                let value = Self::value_at(n, i as i32, j as i32);
                row.push(value);
                j = j + 1;
            }
            result.push(row);
            i = i + 1;
        }
        result
    }
}

}
