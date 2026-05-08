impl Solution {
    pub fn diagonal_sum(mat: Vec<Vec<i32>>) -> i32
    {
        let n = mat.len();
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + mat[i][i];
            if i != n - 1 - i {
                sum = sum + mat[i][n - 1 - i];
            }
            i = i + 1;
        }
        sum
    }
}
