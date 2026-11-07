impl Solution {
    pub fn min_adjacent_pair(heights: Vec<i32>, n: usize) -> (usize, usize) {
        let mut best_i = 0usize;
        let mut best_j = 1usize;
        let d0 = heights[0] - heights[1];
        let mut min_d = if d0 >= 0 { d0 } else { -d0 };
        let mut i = 1usize;
        while i < n {
            let j = if i + 1 < n { i + 1 } else { 0 };
            let d = heights[i] - heights[j];
            let d_abs = if d >= 0 { d } else { -d };
            if d_abs < min_d {
                min_d = d_abs;
                best_i = i;
                best_j = j;
            }
            i += 1;
        }
        (best_i, best_j)
    }
}
