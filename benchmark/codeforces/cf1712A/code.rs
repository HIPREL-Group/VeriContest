impl Solution {
    pub fn min_swaps_minimize_prefix_sum(p: Vec<i32>, n: usize, k: usize) -> i32 {
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < k {
            if p[i] > k as i32 {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}
