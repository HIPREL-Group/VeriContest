impl Solution {
    pub fn min_end(n: i32, x: i32) -> i64 {
        let mut result = x as i64;
        let mut remaining = (n - 1) as i64;
        let mut pos = 0i32;
        let xx = x as i64;

        while pos < 63 && remaining > 0 {
            let position = 1i64 << pos;
            if (xx & position) == 0 {
                if (remaining & 1) == 1 {
                    result = result | position;
                }
                remaining = remaining / 2;
            }
            pos = pos + 1;
        }
        result
    }
}
