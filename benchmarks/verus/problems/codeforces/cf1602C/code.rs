impl Solution {
    pub fn valid_k_values(n: usize, cnt: Vec<i32>) -> Vec<i32> {
        let mut ans: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n {
            let k_i32: i32 = k as i32;
            let mut b: usize = 0;
            let mut bad_idx: i32 = -1;

            while b < 30 {
                if bad_idx == -1 && cnt[b] % k_i32 != 0 {
                    bad_idx = b as i32;
                }
                b = b + 1;
            }

            if bad_idx == -1 {
                ans.push(k as i32);
            }

            k = k + 1;
        }

        ans
    }
}
