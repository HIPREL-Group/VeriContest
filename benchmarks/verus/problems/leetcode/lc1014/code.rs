impl Solution {
    pub fn max_score_sightseeing_pair(values: Vec<i32>) -> i32 {
        let n = values.len();
        let mut best_left = values[0];
        let mut best = values[0] + values[1] - 1;
        let second_left = values[1] + 1;
        if second_left > best_left {
            best_left = second_left;
        }
        let mut j = 2usize;
        while j < n {
            let candidate = best_left + values[j] - j as i32;
            if candidate > best {
                best = candidate;
            }
            let left_candidate = values[j] + j as i32;
            if left_candidate > best_left {
                best_left = left_candidate;
            }
            j += 1;
        }
        best
    }
}
