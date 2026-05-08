impl Solution {
    pub fn min_flagstones(n: u64, m: u64, a: u64) -> u64 {
        let rows = (n + a - 1) / a;
        let cols = (m + a - 1) / a;
        rows * cols
    }
}
