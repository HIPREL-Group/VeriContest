impl Solution {
    pub fn distribute_candies(candy_type: Vec<i32>) -> i32 {
        let mut seen: Vec<bool> = Vec::new();
        let mut fill_idx = 0usize;
        while fill_idx < 200001usize {
            seen.push(false);
            fill_idx += 1;
        }
        let mut distinct = 0i32;
        let n = candy_type.len();
        let mut i = 0usize;
        while i < n {
            let ci = candy_type[i];
            let offset = (ci as i64 + 100_000i64) as usize;
            if !seen[offset] {
                seen[offset] = true;
                distinct += 1;
            }
            i += 1;
        }
        let half = (n / 2) as i32;
        if distinct <= half { distinct } else { half }
    }
}
