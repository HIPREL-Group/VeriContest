impl Solution {
    pub fn chalk_replacer(chalk: Vec<i32>, k: i32) -> i32 {
        let n = chalk.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + chalk[i] as i64;
            i += 1;
        }
        let mut remainder: i64 = k as i64 % total;
        let mut j: usize = 0;
        while j < n {
            if remainder < chalk[j] as i64 {
                return j as i32;
            }
            remainder = remainder - chalk[j] as i64;
            j += 1;
        }
        0
    }
}
