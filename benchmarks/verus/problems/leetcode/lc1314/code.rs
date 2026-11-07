impl Solution {
    pub fn matrix_block_sum(mat: Vec<Vec<i32>>, k: i32) -> Vec<Vec<i32>> {
        let m = mat.len();
        let n = mat[0].len();
        let ku = k as usize;

        let mut prefix: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let above: i32 = if i > 0 { prefix[i - 1][j] } else { 0 };
                let left: i32 = if j > 0 { row[j - 1] } else { 0 };
                let diag: i32 = if i > 0 && j > 0 { prefix[i - 1][j - 1] } else { 0 };
                let val: i32 = mat[i][j] + above + left - diag;
                row.push(val);
                j += 1;
            }
            prefix.push(row);
            i += 1;
        }

        let mut answer: Vec<Vec<i32>> = Vec::new();
        i = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let r1: usize = if i >= ku { i - ku } else { 0 };
                let r2: usize = if i + ku < m { i + ku } else { m - 1 };
                let c1: usize = if j >= ku { j - ku } else { 0 };
                let c2: usize = if j + ku < n { j + ku } else { n - 1 };

                let top_right: i32 = if r1 > 0 { prefix[r1 - 1][c2] } else { 0 };
                let bottom_left: i32 = if c1 > 0 { prefix[r2][c1 - 1] } else { 0 };
                let top_left: i32 = if r1 > 0 && c1 > 0 { prefix[r1 - 1][c1 - 1] } else { 0 };
                let val: i32 = prefix[r2][c2] - top_right - bottom_left + top_left;
                row.push(val);
                j += 1;
            }
            answer.push(row);
            i += 1;
        }

        answer
    }
}
