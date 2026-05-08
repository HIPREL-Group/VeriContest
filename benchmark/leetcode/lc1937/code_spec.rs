use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_spec(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn max_spec(a: int, b: int) -> int {
        if a >= b { a } else { b }
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

    pub open spec fn dp_val(points: Seq<Vec<i32>>, row: int, col: int) -> int
        decreases row + 1, 0nat,
    {
        if row <= 0 {
            points[0][col] as int
        } else {
            let n = points[0].len() as int;
            points[row][col] as int + Self::best_transfer(points, row, col, n - 1)
        }
    }

    pub open spec fn best_transfer(points: Seq<Vec<i32>>, row: int, target: int, up_to: int) -> int
        decreases row, up_to + 1,
    {
        if up_to < 0 {
            i64::MIN as int
        } else {
            Self::max_spec(
                Self::dp_val(points, row - 1, up_to) - Self::abs_spec(up_to - target),
                Self::best_transfer(points, row, target, up_to - 1),
            )
        }
    }

    pub open spec fn max_col(points: Seq<Vec<i32>>, row: int, up_to: int) -> int
        decreases up_to + 1,
    {
        if up_to < 0 {
            i64::MIN as int
        } else {
            Self::max_spec(
                Self::dp_val(points, row, up_to),
                Self::max_col(points, row, up_to - 1),
            )
        }
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
        let m = points.len();
        let n = points[0].len();

        let mut dp: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            dp.push(points[0][j] as i64);
            j += 1;
        }

        let mut i: usize = 1;
        while i < m {
            let mut left: Vec<i64> = Vec::new();
            left.push(dp[0]);
            let mut j: usize = 1;
            while j < n {
                let prev = left[j - 1] - 1;
                let cur = dp[j];
                let val = if prev > cur { prev } else { cur };
                left.push(val);
                j += 1;
            }

            let mut right: Vec<i64> = Vec::new();
            let mut k: usize = 0;
            while k < n {
                right.push(0i64);
                k += 1;
            }
            right.set(n - 1, dp[n - 1]);
            let mut k: usize = 0;
            while k + 1 < n {
                let j = n - 2 - k;
                let nxt = right[j + 1] - 1;
                let cur = dp[j];
                right.set(j, if nxt > cur { nxt } else { cur });
                k += 1;
            }

            let mut new_dp: Vec<i64> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                let best = if left[j] > right[j] { left[j] } else { right[j] };
                new_dp.push(points[i][j] as i64 + best);
                j += 1;
            }

            dp = new_dp;
            i += 1;
        }

        let mut result: i64 = dp[0];
        let mut j: usize = 1;
        while j < n {
            if dp[j] > result {
                result = dp[j];
            }
            j += 1;
        }

        result
    }
}

}
