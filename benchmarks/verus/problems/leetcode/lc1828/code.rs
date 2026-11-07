impl Solution {
    pub fn count_points(points: Vec<Vec<i32>>, queries: Vec<Vec<i32>>) -> Vec<i32> {
        let mut answer: Vec<i32> = Vec::new();
        let mut qi: usize = 0;
        while qi < queries.len() {
            let qx = queries[qi][0];
            let qy = queries[qi][1];
            let r = queries[qi][2];
            let rr = r as i128;
            let rsq = rr * rr;
            let mut count: i32 = 0;
            let mut pi: usize = 0;
            while pi < points.len() {
                let px = points[pi][0] as i128;
                let py = points[pi][1] as i128;
                let dx = px - qx as i128;
                let dy = py - qy as i128;
                let dx2 = dx * dx;
                let dy2 = dy * dy;
                let dist2 = dx2 + dy2;
                let inside = dist2 <= rsq;
                if inside {
                    count += 1;
                }
                pi += 1;
            }
            answer.push(count);
            qi += 1;
        }
        answer
    }
}
