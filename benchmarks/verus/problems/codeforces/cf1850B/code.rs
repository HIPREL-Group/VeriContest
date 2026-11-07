impl Solution {
    pub fn find_winner(a: Vec<u32>, b: Vec<u32>, n: usize) -> usize {
        let mut best_idx: usize = 0;
        let mut best_b: u32 = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n {
            if a[i] <= 10 {
                if !found || b[i] > best_b {
                    best_idx = i;
                    best_b = b[i];
                    found = true;
                }
            }
            i += 1;
        }
        best_idx + 1
    }
}
