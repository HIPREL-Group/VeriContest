impl Solution {
    pub fn binary_gap(n: i32) -> i32 {
        let nu = n as u32;
        let mut m = nu;
        let mut pos: u32 = 0;
        let mut best: u32 = 0;
        let mut last: u32 = 0;
        let mut has_last = false;
        while pos < 31u32 {
            if (m & 1u32) == 1u32 {
                if has_last {
                    let gap = pos - last;
                    if gap > best {
                        best = gap;
                    }
                }
                last = pos;
                has_last = true;
            }
            m = m >> 1u32;
            pos = pos + 1u32;
        }
        best as i32
    }
}
