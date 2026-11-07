impl Solution {
    pub fn count_recon_pairs(n: usize, d: i64, heights: Vec<i64>) -> u64 {
        let mut count: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                let a = heights[i];
                let b = heights[j];
                let diff: i64 = if a >= b { a - b } else { b - a };
                if diff <= d {
                    count = count + 2;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}
