impl Solution {
    pub fn max_dominoes(m: u32, n: u32) -> u32 {
        let mut area: u64 = 0;
        let mut i: u32 = 0;
        while i < m {
            area = area + (n as u64);
            i = i + 1;
        }
        let r = (area / 2) as u32;
        r
    }
}
