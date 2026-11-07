impl Solution {
    pub fn max_pyramid_height(n: u64) -> u64 {
        let mut h: u64 = 0;
        let mut total: u64 = 0;
        let mut done: bool = false;
        while !done {
            if h >= 10001 {
                done = true;
            } else {
                let level = (h + 1) * (h + 2) / 2;
                if total + level > n {
                    done = true;
                } else {
                    total = total + level;
                    h = h + 1;
                }
            }
        }
        h
    }
}
