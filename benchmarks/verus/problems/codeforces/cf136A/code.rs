impl Solution {
    pub fn inverse_presents(p: Vec<i32>, n: usize) -> Vec<i32> {
        let mut result = Vec::new();
        let mut i = 0usize;
        while i < n {
            result.push(0i32);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let idx = (p[i] as usize) - 1;
            result[idx] = (i + 1) as i32;
            i += 1;
        }
        result
    }
}
