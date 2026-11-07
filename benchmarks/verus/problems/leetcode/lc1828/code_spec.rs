use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn point_in_circle(point: Vec<i32>, qx: i32, qy: i32, r: i32) -> bool {
        let dx = point[0] - qx;
        let dy = point[1] - qy;
        dx * dx + dy * dy <= r * r
    }

    pub open spec fn count_points_in_query(points: Seq<Vec<i32>>, qx: i32, qy: i32, r: i32, i: int) -> int
        decreases points.len() - i
    {
        if i >= points.len() {
            0
        } else {
            (if Self::point_in_circle(points[i], qx, qy, r) { 1int } else { 0int })
                + Self::count_points_in_query(points, qx, qy, r, i + 1)
        }
    }

    pub fn count_points(points: Vec<Vec<i32>>, queries: Vec<Vec<i32>>) -> (answer: Vec<i32>)
        requires
            1 <= points.len() <= 500,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int|
                0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 500 && 0 <= points[i][1] <= 500,
            1 <= queries.len() <= 500,
            forall |j: int| 0 <= j < queries.len() ==> #[trigger] queries[j].len() == 3,
            forall |j: int|
                0 <= j < queries.len() ==> 0 <= #[trigger] queries[j][0] <= 500 && 0 <= queries[j][1] <= 500
                    && 1 <= queries[j][2] <= 500,
        ensures
            answer.len() == queries.len(),
            forall |j: int|
                0 <= j < queries.len() ==> 0 <= #[trigger] answer[j] <= points.len()
                    && answer[j] == Self::count_points_in_query(
                    points@,
                    queries[j][0],
                    queries[j][1],
                    queries[j][2],
                    0,
                ),
    {
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

}
