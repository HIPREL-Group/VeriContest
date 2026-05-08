impl Solution {
    pub fn min_triangulation(n: u32) -> u64 {
        let mut sum: u64 = 0;
        let mut i: u32 = 2;
        while i < n {
            let i64v: u64 = i as u64;
            let term: u64 = i64v * (i64v + 1);
            sum = sum + term;
            i = i + 1;
        }
        sum
    }
}
