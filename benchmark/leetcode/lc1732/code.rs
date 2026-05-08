impl Solution {
    pub fn largest_altitude(gain: Vec<i32>) -> i32 {
        let mut max_alt: i32 = 0;
        let mut cur: i32 = 0;
        let n = gain.len();
        let mut i: usize = 0;
        while i < n {
            cur = cur + gain[i];
            if cur > max_alt {
                max_alt = cur;
            }
            i += 1;
        }
        max_alt
    }
}
