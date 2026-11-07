impl Solution {
    pub fn landing_heights(stairs: Vec<i64>, widths: Vec<usize>, heights: Vec<i64>) -> Vec<i64> {
        let mut res = Vec::new();
        let mut current_top = 0i64;
        let mut i = 0usize;
        while i < widths.len() {
            let w = widths[i];
            let stair = stairs[w - 1];
            let base = if stair >= current_top { stair } else { current_top };
            res.push(base);
            current_top = base + heights[i];
            i += 1;
        }
        res
    }
}
