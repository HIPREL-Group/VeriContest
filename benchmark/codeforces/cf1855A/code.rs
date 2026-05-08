impl Solution {
    pub fn min_swaps(p: Vec<i32>) -> i32 {
        let n = p.len();
        let mut c: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if p[i] == (i + 1) as i32 {
                c = c + 1;
            }
            i = i + 1;
        }
        (c + 1) / 2
    }
}
