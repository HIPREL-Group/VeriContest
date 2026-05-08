impl Solution {
    pub fn max_matrix_sum(matrix: Vec<Vec<i32>>) -> i64 {
        let n = matrix.len();
        let mut total_sum: i64 = 0;
        let mut neg_count: i64 = 0;
        let mut min_abs: i64 = 100_001;
        let mut i = 0;
        while i < n {
            let mut j = 0;
            while j < n {
                let val = matrix[i][j] as i64;
                let abs_v = if val < 0 { -val } else { val };
                total_sum = total_sum + abs_v;
                if matrix[i][j] < 0 {
                    neg_count = neg_count + 1;
                }
                if abs_v < min_abs {
                    min_abs = abs_v;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        if neg_count % 2 == 0 {
            total_sum
        } else {
            total_sum - 2 * min_abs
        }
    }
}
