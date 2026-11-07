impl Solution {
    pub fn max_distance(colors: Vec<i32>) -> i32 {
        let n = colors.len();
        let mut result: i32 = 0;
        let mut i = 0;
        while i < n {
            let mut j = n - 1;
            while j > i {
                let dist = (j - i) as i32;
                if colors[i] != colors[j] && dist > result {
                    result = dist;
                }
                j -= 1;
            }
            i += 1;
        }
        result
    }
}
