impl Solution {
    fn value_at(n: i32, row: i32, col: i32) -> i32 {
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

    pub fn generate_matrix(n: i32) -> Vec<Vec<i32>> {
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
