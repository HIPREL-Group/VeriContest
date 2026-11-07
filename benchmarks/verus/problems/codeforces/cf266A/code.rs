impl Solution {
    pub fn min_stones_to_remove(colors: Vec<u8>, n: usize) -> usize {
        let mut count = 0usize;
        let mut i = 0usize;
        while i + 1 < n {
            if colors[i] == colors[i + 1] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}
