impl Solution {
    pub fn min_seconds(left: Vec<u8>, right: Vec<u8>, n: usize) -> usize {
        let mut l_open: usize = 0;
        let mut r_open: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if left[i] == 1u8 {
                l_open = l_open + 1;
            }
            if right[i] == 1u8 {
                r_open = r_open + 1;
            }
            i = i + 1;
        }
        let l_min: usize = if l_open <= n - l_open { l_open } else { n - l_open };
        let r_min: usize = if r_open <= n - r_open { r_open } else { n - r_open };
        l_min + r_min
    }
}
