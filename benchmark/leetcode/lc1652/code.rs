impl Solution {
    pub fn decrypt(code: Vec<i32>, k: i32) -> Vec<i32> {
        let n = code.len();
        let mut result: Vec<i32> = Vec::new();
        if k == 0 {
            let mut i: usize = 0;
            while i < n {
                result.push(0);
                i = i + 1;
            }
            return result;
        }
        let mut sum: i32 = 0;
        if k > 0 {
            let mut j: usize = 0;
            while j < k as usize {
                sum = sum + code[(1 + j) % n];
                j = j + 1;
            }
            result.push(sum);
            let mut i: usize = 1;
            while i < n {
                sum = sum - code[i % n] + code[(i + k as usize) % n];
                result.push(sum);
                i = i + 1;
            }
        } else {
            let abs_k: usize = (-k) as usize;
            let mut j: usize = 0;
            while j < abs_k {
                sum = sum + code[(n - abs_k + j) % n];
                j = j + 1;
            }
            result.push(sum);
            let mut i: usize = 1;
            while i < n {
                sum = sum - code[(i + n - abs_k - 1) % n] + code[(i + n - 1) % n];
                result.push(sum);
                i = i + 1;
            }
        }
        result
    }
}
