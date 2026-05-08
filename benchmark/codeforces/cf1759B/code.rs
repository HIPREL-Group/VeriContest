impl Solution {
    pub fn lost_permutation(b: Vec<u32>, m: usize, s: u32) -> bool {
        let mut sum_b: u32 = 0;
        let mut max_b: u32 = 0;
        let mut i: usize = 0;
        while i < m {
            sum_b += b[i];
            if b[i] > max_b {
                max_b = b[i];
            }
            i += 1;
        }
        let target: u32 = sum_b + s;
        let mut n: u32 = max_b;
        let mut found: bool = false;
        while n <= 100 {
            let n64: u64 = n as u64;
            let prod: u64 = n64 * (n64 + 1);
            if prod / 2 == target as u64 {
                found = true;
            }
            n += 1;
        }
        found
    }
}
