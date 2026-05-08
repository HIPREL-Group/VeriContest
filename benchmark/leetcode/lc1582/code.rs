impl Solution {
    pub fn num_special(mat: Vec<Vec<i32>>) -> i32 {
        let m = mat.len();
        let n = mat[0].len();
        let mut row_sums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut s: i32 = 0;
            let mut j: usize = 0;
            while j < n {
                s = s + mat[i][j];
                j = j + 1;
            }
            row_sums.push(s);
            i = i + 1;
        }
        let mut col_sums: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut s: i32 = 0;
            let mut k: usize = 0;
            while k < m {
                s = s + mat[k][j];
                k = k + 1;
            }
            col_sums.push(s);
            j = j + 1;
        }
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < m {
            let mut j: usize = 0;
            while j < n {
                if mat[i][j] == 1 && row_sums[i] == 1 && col_sums[j] == 1 {
                    count = count + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}
