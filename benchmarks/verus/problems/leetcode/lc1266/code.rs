impl Solution {
    pub fn min_time_to_visit_all_points(points: Vec<Vec<i32>>) -> i32 {
        let n = points.len();
        let mut result: i32 = 0;
        let mut i: usize = 1;
        while i < n {
            let dx_raw = points[i][0] - points[i - 1][0];
            let dx = if dx_raw >= 0 { dx_raw } else { -dx_raw };
            let dy_raw = points[i][1] - points[i - 1][1];
            let dy = if dy_raw >= 0 { dy_raw } else { -dy_raw };
            let dist = if dx >= dy { dx } else { dy };
            result = result + dist;
            i = i + 1;
        }
        result
    }
}
