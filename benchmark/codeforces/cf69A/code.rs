impl Solution {
    pub fn is_equilibrium(vec: Vec<i32>, n: usize) -> bool {
        let mut sum_x = 0i64;
        let mut sum_y = 0i64;
        let mut sum_z = 0i64;
        let mut i = 0usize;
        while i < n {
            sum_x += vec[3 * i] as i64;
            sum_y += vec[3 * i + 1] as i64;
            sum_z += vec[3 * i + 2] as i64;
            i += 1;
        }
        sum_x == 0 && sum_y == 0 && sum_z == 0
    }
}
