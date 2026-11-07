use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    proof fn diff_bound_500(a: i32, b: i32)
        requires
            0 <= a <= 500,
            0 <= b <= 500,
        ensures
            -500 <= a as i128 - b as i128 <= 500,
    {
    }

    proof fn square_bound_500(x: i128)
        requires
            -500 <= x <= 500,
        ensures
            0 <= x * x <= 250000,
    {
        assert(0 <= x * x <= 250000) by (nonlinear_arith)
            requires -500 <= x <= 500;
    }

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
        while qi < queries.len()
            invariant
                0 <= qi <= queries.len(),
                1 <= points.len() <= 500,
                1 <= queries.len() <= 500,
                forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
                forall |i: int|
                    0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 500 && 0 <= points[i][1] <= 500,
                forall |j: int| 0 <= j < queries.len() ==> #[trigger] queries[j].len() == 3,
                forall |j: int|
                    0 <= j < queries.len() ==> 0 <= #[trigger] queries[j][0] <= 500 && 0 <= queries[j][1] <= 500
                        && 1 <= queries[j][2] <= 500,
                answer.len() == qi,
                forall |j: int|
                    0 <= j < qi ==> 0 <= #[trigger] answer[j] <= points.len()
                        && answer[j] == Self::count_points_in_query(
                        points@,
                        queries[j][0],
                        queries[j][1],
                        queries[j][2],
                        0,
                    ),
            decreases queries.len() - qi,
        {
            proof {
                assert(queries[qi as int].len() == 3);
            }
            let qx = queries[qi][0];
            let qy = queries[qi][1];
            let r = queries[qi][2];
            let rr = r as i128;
            proof {
                Self::square_bound_500(rr);
            }
            let rsq = rr * rr;
            let mut count: i32 = 0;
            let mut pi: usize = 0;
            while pi < points.len()
                invariant
                    0 <= qi < queries.len(),
                    0 <= pi <= points.len(),
                    0 <= qx <= 500,
                    0 <= qy <= 500,
                    1 <= r <= 500,
                    rr == r as i128,
                    rsq == rr * rr,
                    1 <= points.len() <= 500,
                    forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
                    forall |i: int|
                        0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 500 && 0 <= points[i][1] <= 500,
                    count == Self::count_points_in_query(points@, qx, qy, r, 0)
                        - Self::count_points_in_query(points@, qx, qy, r, pi as int),
                    0 <= count <= pi,
                decreases points.len() - pi,
            {
                proof {
                    assert(points[pi as int].len() == 2);
                    assert(0 <= points[pi as int][0] <= 500);
                    assert(0 <= points[pi as int][1] <= 500);
                }
                let px = points[pi][0] as i128;
                let py = points[pi][1] as i128;
                let dx = px - qx as i128;
                let dy = py - qy as i128;
                proof {
                    Self::diff_bound_500(points[pi as int][0], qx);
                    Self::diff_bound_500(points[pi as int][1], qy);
                    Self::square_bound_500(dx);
                    Self::square_bound_500(dy);
                }
                let dx2 = dx * dx;
                let dy2 = dy * dy;
                proof {
                    assert(0 <= dx2 <= 250000);
                    assert(0 <= dy2 <= 250000);
                    assert(0 <= dx2 + dy2 <= 500000) by (nonlinear_arith)
                        requires 0 <= dx2 <= 250000, 0 <= dy2 <= 250000;
                }
                let dist2 = dx2 + dy2;
                let inside = dist2 <= rsq;
                if inside {
                    proof {
                        assert(count <= pi);
                        assert(pi < points.len());
                        assert(points.len() <= 500);
                        assert(count < 2147483647) by (nonlinear_arith)
                            requires count <= pi, pi < points.len(), points.len() <= 500;
                    }
                    count += 1;
                }
                proof {
                    assert(Self::count_points_in_query(points@, qx, qy, r, pi as int)
                        == (if Self::point_in_circle(points@[pi as int], qx, qy, r) { 1int } else { 0int })
                        + Self::count_points_in_query(points@, qx, qy, r, pi as int + 1));
                    assert(Self::point_in_circle(points@[pi as int], qx, qy, r)
                        == inside);
                }
                pi += 1;
            }
            proof {
                assert(count == Self::count_points_in_query(points@, qx, qy, r, 0));
            }
            let ghost answer_prev = answer@;
            answer.push(count);
            proof {
                assert(answer@ == answer_prev.push(count));
                assert forall |j: int|
                    0 <= j < qi
                    implies 0 <= answer[j] <= points.len()
                        && answer[j] == Self::count_points_in_query(
                        points@,
                        queries[j][0],
                        queries[j][1],
                        queries[j][2],
                        0,
                    )
                by {
                    assert(answer@[j] == answer_prev[j]);
                };
            }
            qi += 1;
        }
        answer
    }
}

}
