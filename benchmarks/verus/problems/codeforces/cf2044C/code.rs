impl Solution {
    pub fn max_monkeys(m: u64, a: u64, b: u64, c: u64) -> u64 {
        let row1: u64 = if m <= a { m } else { a };
        let row2: u64 = if m <= b { m } else { b };
        let remaining: u64 = 2 * m - row1 - row2;
        let extra: u64 = if c <= remaining { c } else { remaining };
        row1 + row2 + extra
    }
}
