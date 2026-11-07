impl Solution {
    pub fn strong_vertices(a: Vec<i32>, b: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut max_d: i32 = a[0] - b[0];
        let mut result: Vec<i32> = Vec::new();
        result.push(1);

        let mut i: usize = 1;
        while i < n {
            let d = a[i] - b[i];
            if d > max_d {
                max_d = d;
                result = Vec::new();
                result.push((i + 1) as i32);
            } else if d == max_d {
                result.push((i + 1) as i32);
            }
            i = i + 1;
        }

        result
    }
}
