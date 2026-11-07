impl Solution {
    pub fn years_needed(n: usize, d: Vec<u32>, a: usize, b: usize) -> u32 {
        let mut sum: u32 = 0;
        let mut i: usize = a - 1;
        let lo: usize = a - 1;
        let hi: usize = b - 1;
        while i < hi {
            sum += d[i];
            i += 1;
        }
        sum
    }
}
