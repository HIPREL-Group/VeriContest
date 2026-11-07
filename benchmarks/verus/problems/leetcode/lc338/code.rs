impl Solution {
    pub fn count_bits(n: i32) -> Vec<i32> {
        let n_usize = n as usize;
        let mut ans: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n_usize {
            ans.push(0);
            k += 1;
        }
        let mut i: usize = 1;
        while i <= n_usize {
            let half: usize = i / 2;
            let bit: usize = i % 2;
            let v = ans[half] + (bit as i32);
            ans[i] = v;
            i += 1;
        }
        ans
    }
}
