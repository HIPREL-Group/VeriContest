impl Solution {
    pub fn number_of_right_triangles(grid: Vec<Vec<i32>>) -> i64 {
        let m = grid.len();
        let n = grid[0].len();

        let mut row_counts: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row_sum: i64 = 0;
            let mut j: usize = 0;
            while j < n {
                if grid[i][j] == 1 {
                    row_sum = row_sum + 1;
                }
                j = j + 1;
            }
            row_counts.push(row_sum);
            i = i + 1;
        }

        let mut col_counts: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut col_sum: i64 = 0;
            i = 0;
            while i < m {
                if grid[i][j] == 1 {
                    col_sum = col_sum + 1;
                }
                i = i + 1;
            }
            col_counts.push(col_sum);
            j = j + 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < m {
            j = 0;
            while j < n {
                if grid[i][j] == 1 {
                    let add = (row_counts[i] - 1) * (col_counts[j] - 1);
                    ans = ans + add;
                }
                j = j + 1;
            }
            i = i + 1;
        }

        ans
    }
}
