impl Solution {
    pub fn count_advancing(scores: Vec<i32>, k: usize) -> usize {
        let threshold = scores[k - 1];
        let mut count = 0usize;
        let mut i = 0usize;
        while i < scores.len() {
            if scores[i] >= threshold && scores[i] > 0 {
                count += 1;
            }
            i += 1;
        }
        count
    }
}
