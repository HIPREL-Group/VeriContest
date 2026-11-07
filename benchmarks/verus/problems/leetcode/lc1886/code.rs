impl Solution {
    pub fn find_rotation(mat: Vec<Vec<i32>>, target: Vec<Vec<i32>>) -> bool {
        let n = mat.len();
        let mut r0 = true;
        let mut r90 = true;
        let mut r180 = true;
        let mut r270 = true;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                if mat[i][j] != target[i][j] {
                    r0 = false;
                }
                if mat[i][j] != target[j][n - 1 - i] {
                    r90 = false;
                }
                if mat[i][j] != target[n - 1 - i][n - 1 - j] {
                    r180 = false;
                }
                if mat[i][j] != target[n - 1 - j][i] {
                    r270 = false;
                }
                j += 1;
            }
            i += 1;
        }
        r0 || r90 || r180 || r270
    }
}
