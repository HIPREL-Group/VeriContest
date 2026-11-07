impl Solution {
    pub fn compute_min_max_distances(x: Vec<i64>) -> Vec<(i64, i64)> {
        let n = x.len();
        let mut result: Vec<(i64, i64)> = Vec::new();
        let mut i = 0usize;
        while i < n {
            let mini;
            let maxi;
            if i == 0 {
                let d1 = if x[1] >= x[0] { x[1] - x[0] } else { x[0] - x[1] };
                let d2 = if x[n - 1] >= x[0] { x[n - 1] - x[0] } else { x[0] - x[n - 1] };
                mini = d1;
                maxi = d2;
            } else if i == n - 1 {
                let d1 = if x[n - 1] >= x[n - 2] { x[n - 1] - x[n - 2] } else { x[n - 2] - x[n - 1] };
                let d2 = if x[n - 1] >= x[0] { x[n - 1] - x[0] } else { x[0] - x[n - 1] };
                mini = d1;
                maxi = d2;
            } else {
                let left_dist = if x[i] >= x[i - 1] { x[i] - x[i - 1] } else { x[i - 1] - x[i] };
                let right_dist = if x[i + 1] >= x[i] { x[i + 1] - x[i] } else { x[i] - x[i + 1] };
                mini = left_dist.min(right_dist);
                let left_end = if x[i] >= x[0] { x[i] - x[0] } else { x[0] - x[i] };
                let right_end = if x[n - 1] >= x[i] { x[n - 1] - x[i] } else { x[i] - x[n - 1] };
                maxi = left_end.max(right_end);
            }
            result.push((mini, maxi));
            i += 1;
        }
        result
    }
}
