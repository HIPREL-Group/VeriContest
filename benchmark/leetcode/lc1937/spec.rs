use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_spec(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    
    pub open spec fn valid_path(path: Seq<int>, m: int, n: int) -> bool {
        path.len() == m
        && forall|r: int| 0 <= r < m ==> 0 <= #[trigger] path[r] < n
    }

    
    pub open spec fn path_points_sum(
        points: Seq<Vec<i32>>,
        path: Seq<int>,
        up_to: int,
    ) -> int
        decreases up_to + 1,
    {
        if up_to < 0 {
            0
        } else {
            Self::path_points_sum(points, path, up_to - 1)
            + points[up_to][path[up_to]] as int
        }
    }

    
    pub open spec fn path_transition_cost(path: Seq<int>, up_to: int) -> int
        decreases up_to,
    {
        if up_to <= 0 {
            0
        } else {
            Self::path_transition_cost(path, up_to - 1)
            + Self::abs_spec(path[up_to] - path[up_to - 1])
        }
    }

    
    pub open spec fn path_score(points: Seq<Vec<i32>>, path: Seq<int>) -> int {
        Self::path_points_sum(points, path, path.len() as int - 1)
        - Self::path_transition_cost(path, path.len() as int - 1)
    }

    pub fn max_points(points: Vec<Vec<i32>>) -> (res: i64)
        requires
            1 <= points.len() <= 100_000,
            1 <= points[0].len() <= 100_000,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            exists|path: Seq<int>|
                Self::valid_path(path, points@.len() as int, points@[0].len() as int)
                && Self::path_score(points@, path) == res as int,
            forall|path: Seq<int>|
                Self::valid_path(path, points@.len() as int, points@[0].len() as int)
                ==> Self::path_score(points@, path) <= res as int,
    {
    }
}

}
