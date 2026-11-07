impl Solution {
    pub fn strange_table_number(n: u64, m: u64, x: u64) -> u64 {
        let row = (x - 1) % n + 1;
        let col = (x - 1) / n + 1;
        let ans = ((row - 1) as u128) * (m as u128) + (col as u128);
        ans as u64
    }
}
