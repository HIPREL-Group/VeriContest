impl Solution {
    pub fn find_diagonal_order(nums: Vec<Vec<i32>>) -> Vec<i32> {
        let m = nums.len();
        let mut max_d: usize = 0;
        let mut i: usize = m;
        while i > 0 {
            i = i - 1;
            let d = i + nums[i].len() - 1;
            if d > max_d {
                max_d = d;
            }
        }
        let mut result: Vec<i32> = Vec::new();
        let mut d: usize = 0;
        while d <= max_d {
            let start_i: usize = if d < m { d } else { m - 1 };
            let mut ci: usize = start_i + 1;
            while ci > 0 {
                ci = ci - 1;
                if d - ci < nums[ci].len() {
                    result.push(nums[ci][d - ci]);
                }
            }
            d = d + 1;
        }
        result
    }
}
