impl Solution {
    pub fn nearest_valid_point(x: i32, y: i32, points: Vec<Vec<i32>>) -> i32 {
        let n: usize = points.len();
        let mut min_dist: i32 = 30000;
        let mut min_idx: i32 = -1;
        let mut i: usize = 0;
        
        while i < n {
            let px = points[i][0];
            let py = points[i][1];
            if px == x || py == y {
                let dx = if px > x { px - x } else { x - px };
                let dy = if py > y { py - y } else { y - py };
                let d = dx + dy;
                if d < min_dist {
                    min_dist = d;
                    min_idx = i as i32;
                }
            }
            i = i + 1;
        }
        
        min_idx
    }
}
