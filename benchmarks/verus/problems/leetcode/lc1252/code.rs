impl Solution {
    pub fn odd_cells(m: i32, n: i32, indices: Vec<Vec<i32>>) -> i32 {
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
            row_counts[r] = old_r + 1;
            let old_c = col_counts[c];
            col_counts[c] = old_c + 1;
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

