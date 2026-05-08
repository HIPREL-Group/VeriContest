impl Solution {
    pub fn row_and_maximum_ones(mat: Vec<Vec<i32>>) -> Vec<i32> {
        let m = mat.len();
        let mut best_row: usize = 0;
        let mut best_cnt: i32 = 0;
        let mut i: usize = 0;
        while i < m {
            let row_len = mat[i].len();
            let mut c: i32 = 0;
            let mut j: usize = 0;
            while j < row_len {
                if mat[i][j] == 1 {
                    if c < 2147483647 {
                        c = c + 1;
                    }
                }
                j = j + 1;
            }
            if c > best_cnt {
                best_cnt = c;
                best_row = i;
            }
            i = i + 1;
        }
        let mut out: Vec<i32> = Vec::new();
        out.push(best_row as i32);
        out.push(best_cnt);
        out
    }
}
