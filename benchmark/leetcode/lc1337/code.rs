impl Solution {
    pub fn k_weakest_rows(mat: Vec<Vec<i32>>, k: i32) -> Vec<i32> {
        let m = mat.len();
        let n = mat[0].len();
        let mut keys: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut c: i32 = 0;
            let mut j: usize = 0;
            while j < n {
                c = c + mat[i][j];
                j = j + 1;
            }
            keys.push(c * 200 + i as i32);
            i = i + 1;
        }
        if m > 1 {
            let mut outer: usize = 1;
            while outer < m {
                let mut j: usize = outer;
                while j > 0 {
                    if keys[j - 1] > keys[j] {
                        let tmp1 = keys[j];
                        let tmp2 = keys[j - 1];
                        keys[j - 1] = tmp1;
                        keys[j] = tmp2;
                    }
                    j -= 1;
                }
                outer += 1;
            }
        }
        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < k as usize {
            result.push(keys[i] % 200);
            i = i + 1;
        }
        result
    }
}
