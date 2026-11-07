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

    
    pub open spec fn best_transfer_argmax(
        points: Seq<Vec<i32>>,
        row: int,
        target: int,
        up_to: int,
    ) -> int
        decreases up_to + 1,
    {
        if up_to <= 0 {
            0
        } else {
            let candidate = Self::dp_val(points, row - 1, up_to)
                - Self::abs_spec(up_to - target);
            let prev_best = Self::best_transfer(points, row, target, up_to - 1);
            if candidate >= prev_best {
                up_to
            } else {
                Self::best_transfer_argmax(points, row, target, up_to - 1)
            }
        }
    }

    
    pub open spec fn optimal_path(
        points: Seq<Vec<i32>>,
        row: int,
        col: int,
        n: int,
    ) -> Seq<int>
        decreases row + 1,
    {
        if row <= 0 {
            seq![col]
        } else {
            let prev_col = Self::best_transfer_argmax(points, row, col, n - 1);
            Self::optimal_path(points, row - 1, prev_col, n).push(col)
        }
    }

    
    pub open spec fn max_col_argmax(
        points: Seq<Vec<i32>>,
        row: int,
        up_to: int,
    ) -> int
        decreases up_to + 1,
    {
        if up_to <= 0 {
            0
        } else {
            let cur = Self::dp_val(points, row, up_to);
            let prev_best = Self::max_col(points, row, up_to - 1);
            if cur >= prev_best {
                up_to
            } else {
                Self::max_col_argmax(points, row, up_to - 1)
            }
        }
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

    pub open spec fn left_max(dp: Seq<i64>, j: int) -> int
        decreases j + 1,
    {
        if j <= 0 {
            dp[0] as int
        } else {
            Self::max_spec(Self::left_max(dp, j - 1) - 1, dp[j] as int)
        }
    }

    pub open spec fn right_max(dp: Seq<i64>, j: int, n: int) -> int
        decreases n - j,
    {
        if j >= n - 1 {
            dp[j] as int
        } else {
            Self::max_spec(Self::right_max(dp, j + 1, n) - 1, dp[j] as int)
        }
    }

    pub open spec fn bt_dp(dp: Seq<i64>, target: int, up_to: int) -> int
        decreases up_to + 1,
    {
        if up_to < 0 {
            i64::MIN as int
        } else {
            Self::max_spec(
                dp[up_to] as int - Self::abs_spec(up_to - target),
                Self::bt_dp(dp, target, up_to - 1),
            )
        }
    }

    proof fn dp_val_bounds(points: Seq<Vec<i32>>, row: int, col: int)
        requires
            0 <= row < points.len() as int,
            0 <= col < points[0].len() as int,
            points.len() >= 1,
            points[0].len() >= 1,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            0 <= Self::dp_val(points, row, col) <= (row + 1) * 100_000,
        decreases row + 1, 0nat,
    {
        if row <= 0 {
        } else {
            let n = points[0].len() as int;
            Self::best_transfer_bounds(points, row, col, n - 1);
            Self::best_transfer_ge_at_target(points, row, col, n - 1);
            Self::dp_val_bounds(points, row - 1, col);
        }
    }

    proof fn best_transfer_ge_at_target(
        points: Seq<Vec<i32>>,
        row: int,
        target: int,
        up_to: int,
    )
        requires
            row >= 1,
            0 <= target <= up_to,
            up_to < points[0].len() as int,
            0 < points.len(),
            0 < points[0].len(),
            points.len() * points[0].len() <= 100_000,
            row - 1 < points.len(),
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            Self::best_transfer(points, row, target, up_to) >= Self::dp_val(points, row - 1, target),
        decreases up_to - target,
    {
        if up_to == target {
            assert(Self::abs_spec(target - target) == 0);
        } else {
            Self::best_transfer_ge_at_target(points, row, target, up_to - 1);
        }
    }

    proof fn best_transfer_bounds(points: Seq<Vec<i32>>, row: int, target: int, up_to: int)
        requires
            row >= 1,
            0 <= target < points[0].len(),
            -1 <= up_to < points[0].len(),
            0 < points.len(),
            0 < points[0].len(),
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
            row - 1 < points.len(),
        ensures
            Self::best_transfer(points, row, target, up_to) <= row * 100_000,
            up_to >= 0 ==> Self::best_transfer(points, row, target, up_to) >= -(points[0].len() as int),
        decreases row, up_to + 1,
    {
        if up_to < 0 {
            assert(Self::best_transfer(points, row, target, up_to) == i64::MIN as int);
            assert(i64::MIN as int <= row * 100_000) by (nonlinear_arith)
                requires row >= 1;
        } else {
            let d = Self::dp_val(points, row - 1, up_to);
            let a = Self::abs_spec(up_to - target);
            let cur = d - a;
            let prev = Self::best_transfer(points, row, target, up_to - 1);
            assert(Self::best_transfer(points, row, target, up_to) == Self::max_spec(cur, prev));
            Self::dp_val_bounds(points, row - 1, up_to);
            assert(d <= (row - 1 + 1) * 100_000);
            assert((row - 1 + 1) * 100_000 == row * 100_000) by (nonlinear_arith)
                requires row >= 1;
            assert(a >= 0);
            assert(cur + a == d) by (nonlinear_arith)
                requires cur == d - a;
            assert(cur + a <= row * 100_000);
            assert(cur <= row * 100_000) by (nonlinear_arith)
                requires
                    cur + a <= row * 100_000,
                    a >= 0;
            assert(cur <= row * 100_000);

            if up_to == 0 {
                assert(up_to - 1 == -1);
                assert(prev == i64::MIN as int);
                assert(i64::MIN as int <= 0);
                assert(prev <= 0);
                assert(0 <= row * 100_000) by (nonlinear_arith)
                    requires row >= 1;
                assert(prev <= row * 100_000);
            }
            if up_to > 0 {
                Self::best_transfer_bounds(points, row, target, up_to - 1);
                assert(prev <= row * 100_000);
            }

            if cur >= prev {
                assert(Self::max_spec(cur, prev) == cur);
            } else {
                assert(Self::max_spec(cur, prev) == prev);
            }
            assert(Self::best_transfer(points, row, target, up_to) <= row * 100_000);
        }
    }

    proof fn bt_dp_matches_best_transfer(
        points: Seq<Vec<i32>>,
        dp: Seq<i64>,
        row: int,
        target: int,
        up_to: int,
    )
        requires
            row >= 1,
            -1 <= up_to,
            up_to < dp.len(),
            dp.len() == points[0].len(),
            forall|k: int| 0 <= k < dp.len() ==> #[trigger] dp[k] as int == Self::dp_val(points, row - 1, k),
        ensures
            Self::bt_dp(dp, target, up_to) == Self::best_transfer(points, row, target, up_to),
        decreases up_to + 1,
    {
        if up_to < 0 {
        } else {
            Self::bt_dp_matches_best_transfer(points, dp, row, target, up_to - 1);
        }
    }

    proof fn left_max_is_bt_dp_left(dp: Seq<i64>, target: int, up_to: int)
        requires
            0 <= up_to <= target,
            target < dp.len(),
            dp.len() <= 100_000,
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            Self::left_max(dp, up_to) == Self::bt_dp(dp, target, up_to) + (target - up_to),
        decreases up_to + 1,
    {
        if up_to <= 0 {
            assert(Self::left_max(dp, 0) == dp[0] as int);
            assert(Self::bt_dp(dp, target, 0) == Self::max_spec(
                dp[0] as int - Self::abs_spec(0 - target),
                Self::bt_dp(dp, target, -1),
            ));
            assert(Self::bt_dp(dp, target, -1) == i64::MIN as int);
            assert(Self::abs_spec(0 - target) == target);
            assert(dp[0] as int >= 0);
            assert(target < dp.len());
            assert(dp[0] as int - target >= 0 - dp.len() as int);
            assert(dp[0] as int - target > i64::MIN as int);
            assert(Self::bt_dp(dp, target, 0) == dp[0] as int - target);
            assert(Self::left_max(dp, 0) == Self::bt_dp(dp, target, 0) + target);
        } else {
            Self::left_max_is_bt_dp_left(dp, target, up_to - 1);
        }
    }

    proof fn right_max_is_bt_dp_right(dp: Seq<i64>, target: int, from: int, n: int)
        requires
            target <= from,
            from < n,
            n == dp.len() as int,
            n >= 1,
        ensures
            Self::right_max(dp, from, n) == Self::bt_dp_right(dp, target, from, n) + (from - target),
        decreases n - from,
    {
        if from >= n - 1 {
            assert(Self::right_max(dp, from, n) == dp[from] as int);
            assert(Self::bt_dp_right(dp, target, from, n)
                == dp[from] as int - Self::abs_spec(from - target));
            assert(Self::abs_spec(from - target) == from - target);
        } else {
            Self::right_max_is_bt_dp_right(dp, target, from + 1, n);
        }
    }

    pub open spec fn bt_dp_right(dp: Seq<i64>, target: int, from: int, n: int) -> int
        decreases n - from,
    {
        if from >= n {
            i64::MIN as int
        } else if from >= n - 1 {
            dp[from] as int - Self::abs_spec(from - target)
        } else {
            Self::max_spec(
                dp[from] as int - Self::abs_spec(from - target),
                Self::bt_dp_right(dp, target, from + 1, n),
            )
        }
    }

    proof fn bt_dp_split(dp: Seq<i64>, target: int, n: int)
        requires
            0 <= target < n,
            n <= dp.len() as int,
            n >= 1,
            n <= 100_000,
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            Self::bt_dp(dp, target, n - 1) == Self::max_spec(
                Self::bt_dp(dp, target, target),
                Self::bt_dp_right(dp, target, target + 1, n),
            ),
        decreases n - 1 - target,
    {
        if n - 1 == target {
            assert(Self::bt_dp_right(dp, target, target + 1, n) == i64::MIN as int);
        } else {
            Self::bt_dp_split(dp, target, n - 1);
            Self::bt_dp_right_extend(dp, target, target + 1, n);
        }
    }

    proof fn bt_dp_right_extend(dp: Seq<i64>, target: int, from: int, n: int)
        requires
            0 <= target,
            target < from,
            from < n,
            n <= dp.len() as int,
            n >= 1,
            n <= 100_000,
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            Self::max_spec(
                dp[n - 1] as int - Self::abs_spec((n - 1) - target),
                Self::bt_dp_right(dp, target, from, n - 1),
            ) == Self::bt_dp_right(dp, target, from, n),
        decreases n - from,
    {
        if from >= n - 1 {
            assert(target < from);
            assert(from >= n - 1);
            assert(from < n);
            assert(target <= n - 2);
            assert((n - 1) - target >= 1);
            assert(Self::abs_spec((n - 1) - target) == (n - 1) - target);
            assert((n - 1) - target <= n - 1);
            assert(n - 1 < n);
            assert(dp[n - 1] as int >= 0);
            assert(dp[n - 1] as int - Self::abs_spec((n - 1) - target) >= -(n as int));
            assert(dp[n - 1] as int - Self::abs_spec((n - 1) - target) > i64::MIN as int);
        } else {
            Self::bt_dp_right_extend(dp, target, from + 1, n);
        }
    }

    proof fn split_final(dp: Seq<i64>, target: int, n: int)
        requires
            0 <= target < n,
            n == dp.len() as int,
            n >= 1,
            n <= 100_000,
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            Self::bt_dp(dp, target, n - 1) == Self::max_spec(
                Self::left_max(dp, target),
                Self::right_max(dp, target, n),
            ),
    {
        assert(dp.len() <= 100_000) by {
            assert(dp.len() == n);
        };
        Self::bt_dp_split(dp, target, n);
        Self::left_max_is_bt_dp_left(dp, target, target);
        Self::right_max_is_bt_dp_right(dp, target, target, n);
        assert(Self::bt_dp(dp, target, target) == Self::left_max(dp, target) - (target - target));
        assert(target - target == 0int);

        Self::bt_dp_right_includes_target(dp, target, n);
    }

    proof fn bt_dp_right_includes_target(dp: Seq<i64>, target: int, n: int)
        requires
            0 <= target < n,
            n == dp.len() as int,
            n <= 100_000,
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            Self::max_spec(
                Self::bt_dp(dp, target, target),
                Self::bt_dp_right(dp, target, target + 1, n),
            ) == Self::max_spec(
                Self::left_max(dp, target),
                Self::right_max(dp, target, n),
            ),
    {
        Self::left_max_is_bt_dp_left(dp, target, target);
        assert(Self::left_max(dp, target) == Self::bt_dp(dp, target, target) + 0);

        if target + 1 >= n {
            assert(Self::bt_dp_right(dp, target, target + 1, n) == i64::MIN as int);
            assert(Self::right_max(dp, target, n) == dp[target] as int);
            assert(Self::bt_dp(dp, target, target) == Self::max_spec(
                dp[target] as int - Self::abs_spec(target - target),
                Self::bt_dp(dp, target, target - 1),
            ));
            assert(Self::abs_spec(target - target) == 0);
        } else {
            Self::right_max_is_bt_dp_right(dp, target, target, n);
            assert(Self::right_max(dp, target, n) == Self::bt_dp_right(dp, target, target, n) + 0);
            Self::bt_dp_right_peel(dp, target, n);
        }
    }

    proof fn bt_dp_right_peel(dp: Seq<i64>, target: int, n: int)
        requires
            0 <= target,
            target + 1 < n,
            n == dp.len() as int,
        ensures
            Self::max_spec(
                Self::bt_dp(dp, target, target),
                Self::bt_dp_right(dp, target, target + 1, n),
            ) == Self::max_spec(
                Self::bt_dp(dp, target, target),
                Self::bt_dp_right(dp, target, target, n),
            ),
    {
        assert(Self::bt_dp_right(dp, target, target, n) == Self::max_spec(
            dp[target] as int - Self::abs_spec(target - target),
            Self::bt_dp_right(dp, target, target + 1, n),
        ));
        assert(Self::abs_spec(target - target) == 0);
        let a = Self::bt_dp(dp, target, target);
        let b = dp[target] as int;
        let c = Self::bt_dp_right(dp, target, target + 1, n);

        assert(Self::bt_dp(dp, target, target) == Self::max_spec(
            dp[target] as int - 0,
            Self::bt_dp(dp, target, target - 1),
        ));
        assert(a >= b);
    }

    proof fn dp_bounds_all(
        points: Seq<Vec<i32>>,
        dp: Seq<i64>,
        row: int,
        n: int,
    )
        requires
            0 <= row < points.len() as int,
            n == points[0].len() as int,
            dp.len() == n,
            points.len() >= 1,
            points[0].len() >= 1,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
            forall|k: int| 0 <= k < n ==> #[trigger] dp[k] as int == Self::dp_val(points, row, k),
        ensures
            forall|k: int| 0 <= k < n ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
    {
        assert forall|k: int| 0 <= k < n implies 0 <= #[trigger] dp[k] <= 10_000_000_000i64 by {
            Self::dp_val_bounds(points, row, k);
            assert(dp[k] as int == Self::dp_val(points, row, k));
            assert(0 <= Self::dp_val(points, row, k) <= (row + 1) * 100_000);
            assert(row + 1 <= points.len());
            assert(points[0int].len() >= 1);
            assert(points.len() <= points.len() * points[0int].len()) by(nonlinear_arith)
                requires points.len() >= 0, points[0int].len() >= 1;
            assert(points.len() <= 100_000);
            assert((row + 1) * 100_000 <= points.len() * 100_000) by(nonlinear_arith)
                requires row + 1 <= points.len();
            assert(points.len() * 100_000 <= 10_000_000_000int) by(nonlinear_arith)
                requires points.len() <= 100_000;
        };
    }

    proof fn left_max_bounds(dp: Seq<i64>, j: int)
        requires
            0 <= j < dp.len(),
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            0 <= Self::left_max(dp, j) <= 10_000_000_000,
        decreases j + 1,
    {
        if j <= 0 {
        } else {
            Self::left_max_bounds(dp, j - 1);
        }
    }

    proof fn right_max_bounds(dp: Seq<i64>, j: int, n: int)
        requires
            0 <= j < n,
            n == dp.len() as int,
            forall|k: int| 0 <= k < dp.len() ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
        ensures
            0 <= Self::right_max(dp, j, n) <= 10_000_000_000,
        decreases n - j,
    {
        if j >= n - 1 {
        } else {
            Self::right_max_bounds(dp, j + 1, n);
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
            res as int == Self::max_col(
                points@,
                (points@.len() - 1) as int,
                (points@[0].len() - 1) as int,
            ),
    {
        let m = points.len();
        let n = points[0].len();

        let mut dp: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                m == points.len(),
                m >= 1,
                n == points[0].len(),
                dp.len() == j,
                forall|r: int|
                    0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
                forall|r: int, c: int|
                    0 <= r < points.len() && 0 <= c < points[0].len()
                        ==> 0 <= #[trigger] points[r][c] <= 100_000,
                forall|k: int| 0 <= k < j as int ==> #[trigger] dp[k] as int == points[0][k] as int,
            decreases n - j,
        {
            dp.push(points[0][j] as i64);
            j += 1;
        }

        assert(forall|k: int|
            0 <= k < n ==> #[trigger] dp[k] as int == Self::dp_val(points@, 0, k));

        let mut i: usize = 1;
        while i < m
            invariant
                1 <= i <= m,
                m == points.len(),
                n == points[0].len(),
                n >= 1,
                m >= 1,
                m * n <= 100_000,
                dp.len() == n,
                forall|r: int|
                    0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
                forall|r: int, c: int|
                    0 <= r < points.len() && 0 <= c < points[0].len()
                        ==> 0 <= #[trigger] points[r][c] <= 100_000,
                forall|k: int|
                    0 <= k < n as int
                        ==> #[trigger] dp[k] as int == Self::dp_val(points@, (i - 1) as int, k),
                forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
            decreases m - i,
        {
            let ghost old_dp = dp@;

            proof {
                Self::dp_bounds_all(points@, dp@, (i - 1) as int, n as int);
            }

            let mut left: Vec<i64> = Vec::new();
            left.push(dp[0]);
            let mut j: usize = 1;
            while j < n
                invariant
                    1 <= j <= n,
                    m >= 1,
                    m == points.len(),
                    n == points[0].len(),
                    n >= 1,
                    dp.len() == n,
                    left.len() == j,
                    old_dp == dp@,
                    forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
                    forall|k: int|
                        0 <= k < j as int
                            ==> #[trigger] left[k] as int == Self::left_max(dp@, k),
                decreases n - j,
            {
                let prev = left[j - 1] - 1;
                let cur = dp[j];
                let val = if prev > cur { prev } else { cur };
                left.push(val);
                j += 1;
            }

            let mut right: Vec<i64> = Vec::new();
            let mut k: usize = 0;
            while k < n
                invariant
                    0 <= k <= n,
                    right.len() == k,
                decreases n - k,
            {
                right.push(0i64);
                k += 1;
            }
            right.set(n - 1, dp[n - 1]);

            let mut k: usize = 0;

            assert(n <= 100_000) by {
                assert(m >= 1);
                assert(n <= m * n) by(nonlinear_arith) requires m >= 1, n >= 0;
            };

            while k + 1 < n
                invariant
                    0 <= k <= n,
                    right.len() == n,
                    dp.len() == n,
                    n >= 1,
                    n <= 100_000,
                    old_dp == dp@,
                    forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
                    right[n as int - 1] as int == Self::right_max(dp@, (n - 1) as int, n as int),
                    forall|j2: int|
                        (n as int - 1 - k as int) <= j2 < n as int
                            ==> #[trigger] right[j2] as int == Self::right_max(dp@, j2, n as int),
                decreases n - 1 - k,
            {
                let j = n - 2 - k;
                let nxt = right[j + 1] - 1;
                let cur = dp[j];
                right.set(j, if nxt > cur { nxt } else { cur });

                assert(right[j as int] as int == Self::right_max(dp@, j as int, n as int));

                k += 1;
            }

            let mut new_dp: Vec<i64> = Vec::new();
            let mut j: usize = 0;

            assert(n <= 100_000) by {
                assert(m >= 1);
                assert(n <= m * n) by(nonlinear_arith) requires m >= 1, n >= 0;
            };

            while j < n
                invariant
                    0 <= j <= n,
                    n == points[0].len(),
                    n >= 1,
                    n <= 100_000,
                    m == points.len(),
                    m >= 1,
                    1 <= i < m,
                    dp.len() == n,
                    left.len() == n,
                    right.len() == n,
                    new_dp.len() == j,
                    old_dp == dp@,
                    forall|r: int|
                        0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
                    forall|r: int, c: int|
                        0 <= r < points.len() && 0 <= c < points[0].len()
                            ==> 0 <= #[trigger] points[r][c] <= 100_000,
                    m * n <= 100_000,
                    forall|k: int|
                        0 <= k < n as int
                            ==> #[trigger] dp[k] as int == Self::dp_val(points@, (i - 1) as int, k),
                    forall|k: int|
                        0 <= k < n as int
                            ==> #[trigger] left[k] as int == Self::left_max(dp@, k),
                    forall|k: int|
                        0 <= k < n as int
                            ==> #[trigger] right[k] as int == Self::right_max(dp@, k, n as int),
                    forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
                    forall|k: int|
                        0 <= k < j as int
                            ==> #[trigger] new_dp[k] as int == Self::dp_val(points@, i as int, k),
                    forall|k: int|
                        0 <= k < j as int ==> 0 <= #[trigger] new_dp[k] <= 10_000_000_000i64,
                decreases n - j,
            {
                proof {
                    Self::left_max_bounds(dp@, j as int);
                    Self::right_max_bounds(dp@, j as int, n as int);
                    Self::split_final(dp@, j as int, n as int);
                    Self::bt_dp_matches_best_transfer(
                        points@,
                        dp@,
                        i as int,
                        j as int,
                        (n - 1) as int,
                    );
                    assert(Self::bt_dp(dp@, j as int, (n - 1) as int)
                        == Self::best_transfer(points@, i as int, j as int, (n - 1) as int));
                    assert(Self::bt_dp(dp@, j as int, (n - 1) as int) == Self::max_spec(
                        Self::left_max(dp@, j as int),
                        Self::right_max(dp@, j as int, n as int),
                    ));
                    assert(Self::best_transfer(points@, i as int, j as int, (n - 1) as int)
                        == Self::max_spec(
                        Self::left_max(dp@, j as int),
                        Self::right_max(dp@, j as int, n as int),
                    ));

                    Self::dp_val_bounds(points@, i as int, j as int);
                    assert(0 <= Self::dp_val(points@, i as int, j as int) <= ((i as int) + 1) * 100_000);
                    assert((i as int) + 1 <= points@.len());
                    assert(points@[0int].len() >= 1);
                    assert(points@.len() <= points@.len() * points@[0int].len()) by(nonlinear_arith)
                        requires points@.len() >= 0, points@[0int].len() >= 1;
                    assert(points@.len() <= 100_000);
                    assert(((i as int) + 1) * 100_000 <= points@.len() * 100_000) by(nonlinear_arith)
                        requires (i as int) + 1 <= points@.len();
                    assert(points@.len() * 100_000 <= 10_000_000_000int) by(nonlinear_arith)
                        requires points@.len() <= 100_000;
                }

                let best = if left[j] > right[j] { left[j] } else { right[j] };
                new_dp.push(points[i][j] as i64 + best);

                assert(new_dp[j as int] as int == Self::dp_val(points@, i as int, j as int));

                j += 1;
            }

            dp = new_dp;

            proof {
                Self::dp_bounds_all(points@, dp@, i as int, n as int);
            }

            i += 1;
        }

        let mut result: i64 = dp[0];

        assert(result as int == Self::dp_val(points@, (m - 1) as int, 0));

        proof {
            assert(Self::max_col(points@, (m - 1) as int, -1int) == i64::MIN as int);
            assert(Self::max_col(points@, (m - 1) as int, 0int) == Self::max_spec(
                Self::dp_val(points@, (m - 1) as int, 0int),
                Self::max_col(points@, (m - 1) as int, -1int),
            ));
            assert(dp[0] >= 0);
            assert(dp[0] as int > i64::MIN as int);
            assert(Self::max_col(points@, (m - 1) as int, 0int) == dp[0] as int);
            assert(result as int == Self::max_col(points@, (m - 1) as int, 0int));
        }

        let mut j: usize = 1;
        while j < n
            invariant
                1 <= j <= n,
                m >= 1,
                n == points[0].len(),
                n >= 1,
                m == points.len(),
                dp.len() == n,
                forall|k: int|
                    0 <= k < n as int
                        ==> #[trigger] dp[k] as int == Self::dp_val(points@, (m - 1) as int, k),
                result as int == Self::max_col(points@, (m - 1) as int, (j - 1) as int),
                forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] dp[k] <= 10_000_000_000i64,
                0 <= result <= 10_000_000_000i64,
            decreases n - j,
        {
            if dp[j] > result {
                result = dp[j];
            }
            j += 1;
        }

        
        proof {
            let m_int = m as int;
            let n_int = n as int;

            
            Self::max_col_argmax_achieves(points@, m_int - 1, n_int - 1);
            let best_col = Self::max_col_argmax(points@, m_int - 1, n_int - 1);
            Self::optimal_path_valid(points@, m_int - 1, best_col, n_int);
            Self::optimal_path_score(points@, m_int - 1, best_col, n_int);
            let opt = Self::optimal_path(points@, m_int - 1, best_col, n_int);
            assert(Self::valid_path(opt, m_int, n_int));
            assert(Self::path_score(points@, opt) == Self::dp_val(points@, m_int - 1, best_col));
            assert(Self::dp_val(points@, m_int - 1, best_col) == Self::max_col(points@, m_int - 1, n_int - 1));
            assert(Self::path_score(points@, opt) == result as int);

            
            assert forall|path: Seq<int>| #![auto]
                Self::valid_path(path, m_int, n_int)
                implies Self::path_score(points@, path) <= result as int
            by {
                Self::dp_val_upper_bound(points@, path, m_int - 1, n_int);
                Self::max_col_ge_dp_val(points@, m_int - 1, n_int - 1, path[m_int - 1]);
            };
        }

        result
    }

    

    
    proof fn best_transfer_ge_at_col(
        points: Seq<Vec<i32>>,
        row: int,
        target: int,
        up_to: int,
        col: int,
    )
        requires
            0 <= col <= up_to,
            up_to < points[0].len() as int,
            row >= 1,
            row - 1 < points.len() as int,
            points.len() >= 1,
            points[0].len() >= 1,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
        ensures
            Self::best_transfer(points, row, target, up_to)
                >= Self::dp_val(points, row - 1, col) - Self::abs_spec(col - target),
        decreases up_to - col,
    {
        if up_to == col {
        } else {
            Self::best_transfer_ge_at_col(points, row, target, up_to - 1, col);
        }
    }

    
    proof fn max_col_ge_dp_val(
        points: Seq<Vec<i32>>,
        row: int,
        up_to: int,
        col: int,
    )
        requires
            0 <= col <= up_to,
        ensures
            Self::max_col(points, row, up_to) >= Self::dp_val(points, row, col),
        decreases up_to - col,
    {
        if up_to == col {
        } else {
            Self::max_col_ge_dp_val(points, row, up_to - 1, col);
        }
    }

    
    proof fn max_col_argmax_achieves(
        points: Seq<Vec<i32>>,
        row: int,
        up_to: int,
    )
        requires
            up_to >= 0,
            0 <= row < points.len() as int,
            points.len() >= 1,
            points[0].len() >= 1,
            up_to < points[0].len() as int,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            0 <= Self::max_col_argmax(points, row, up_to) <= up_to,
            Self::dp_val(points, row, Self::max_col_argmax(points, row, up_to))
                == Self::max_col(points, row, up_to),
        decreases up_to + 1,
    {
        if up_to <= 0 {
            Self::dp_val_bounds(points, row, 0);
            assert(Self::max_col(points, row, -1int) == i64::MIN as int);
            assert(Self::dp_val(points, row, 0) >= 0);
        } else {
            Self::max_col_argmax_achieves(points, row, up_to - 1);
        }
    }

    
    proof fn best_transfer_argmax_achieves(
        points: Seq<Vec<i32>>,
        row: int,
        target: int,
        up_to: int,
    )
        requires
            up_to >= 0,
            row >= 1,
            row - 1 < points.len() as int,
            points.len() >= 1,
            points[0].len() >= 1,
            up_to < points[0].len() as int,
            0 <= target < points[0].len() as int,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            0 <= Self::best_transfer_argmax(points, row, target, up_to) <= up_to,
            Self::dp_val(points, row - 1, Self::best_transfer_argmax(points, row, target, up_to))
                - Self::abs_spec(Self::best_transfer_argmax(points, row, target, up_to) - target)
                == Self::best_transfer(points, row, target, up_to),
        decreases up_to + 1,
    {
        if up_to <= 0 {
            Self::dp_val_bounds(points, row - 1, 0);
            assert(Self::best_transfer(points, row, target, -1int) == i64::MIN as int);
            assert(Self::dp_val(points, row - 1, 0) >= 0);
            assert(Self::abs_spec(0 - target) >= 0);
            assert(Self::dp_val(points, row - 1, 0) - Self::abs_spec(0 - target)
                >= -(target));
            assert(target < points[0].len() as int);
            assert(points[0].len() as int <= points.len() * points[0].len()) by(nonlinear_arith)
                requires points.len() >= 1, points[0].len() >= 0;
            assert(points.len() * points[0].len() <= 100_000);
        } else {
            Self::best_transfer_argmax_achieves(points, row, target, up_to - 1);
        }
    }

    
    proof fn path_points_sum_agree(
        points: Seq<Vec<i32>>,
        path1: Seq<int>,
        path2: Seq<int>,
        up_to: int,
    )
        requires
            up_to >= -1,
            forall|i: int| 0 <= i <= up_to ==> path1[i] == path2[i],
        ensures
            Self::path_points_sum(points, path1, up_to)
                == Self::path_points_sum(points, path2, up_to),
        decreases up_to + 1,
    {
        if up_to < 0 {
        } else {
            Self::path_points_sum_agree(points, path1, path2, up_to - 1);
        }
    }

    
    proof fn path_transition_cost_agree(
        path1: Seq<int>,
        path2: Seq<int>,
        up_to: int,
    )
        requires
            up_to >= 0,
            forall|i: int| 0 <= i <= up_to ==> path1[i] == path2[i],
        ensures
            Self::path_transition_cost(path1, up_to)
                == Self::path_transition_cost(path2, up_to),
        decreases up_to,
    {
        if up_to <= 0 {
        } else {
            Self::path_transition_cost_agree(path1, path2, up_to - 1);
        }
    }

    
    proof fn path_score_decompose(
        points: Seq<Vec<i32>>,
        path: Seq<int>,
        row: int,
    )
        requires
            row >= 1,
            path.len() == row + 1,
        ensures
            Self::path_score(points, path) ==
                Self::path_score(points, path.subrange(0, row))
                + points[row][path[row]] as int
                - Self::abs_spec(path[row] - path[row - 1]),
    {
        let prefix = path.subrange(0, row);
        assert(prefix.len() == row);
        assert forall|i: int| 0 <= i <= row - 1 implies path[i] == prefix[i] by {};
        Self::path_points_sum_agree(points, path, prefix, row - 1);
        Self::path_transition_cost_agree(path, prefix, row - 1);

        
        
        assert(Self::path_points_sum(points, path, row)
            == Self::path_points_sum(points, path, row - 1) + points[row][path[row]] as int);
        
        assert(Self::path_transition_cost(path, row)
            == Self::path_transition_cost(path, row - 1) + Self::abs_spec(path[row] - path[row - 1]));

        
        assert(Self::path_score(points, path) ==
            Self::path_points_sum(points, path, row) - Self::path_transition_cost(path, row));

        
        assert(Self::path_score(points, prefix) ==
            Self::path_points_sum(points, prefix, row - 1) - Self::path_transition_cost(prefix, row - 1));
    }

    
    proof fn dp_val_upper_bound(
        points: Seq<Vec<i32>>,
        path: Seq<int>,
        row: int,
        n: int,
    )
        requires
            0 <= row < points.len() as int,
            path.len() == row + 1,
            n == points[0].len() as int,
            n >= 1,
            points.len() >= 1,
            forall|r: int| 0 <= r < row + 1 ==> 0 <= #[trigger] path[r] < n,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
        ensures
            Self::path_score(points, path) <= Self::dp_val(points, row, path[row]),
        decreases row,
    {
        if row <= 0 {
            
            
            assert(Self::path_points_sum(points, path, 0)
                == Self::path_points_sum(points, path, -1int) + points[0][path[0]] as int);
            assert(Self::path_points_sum(points, path, -1int) == 0);
            assert(Self::path_transition_cost(path, 0) == 0);
        } else {
            let prefix = path.subrange(0, row);
            assert(prefix.len() == row);
            assert(prefix[row - 1] == path[row - 1]);
            assert forall|r: int| 0 <= r < row implies 0 <= #[trigger] prefix[r] < n by {};
            Self::dp_val_upper_bound(points, prefix, row - 1, n);
            Self::path_score_decompose(points, path, row);
            Self::best_transfer_ge_at_col(
                points, row, path[row], n - 1, path[row - 1],
            );
        }
    }

    
    proof fn optimal_path_valid(
        points: Seq<Vec<i32>>,
        row: int,
        col: int,
        n: int,
    )
        requires
            0 <= row < points.len() as int,
            0 <= col < n,
            n == points[0].len() as int,
            n >= 1,
            points.len() >= 1,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            Self::valid_path(Self::optimal_path(points, row, col, n), row + 1, n),
            Self::optimal_path(points, row, col, n).len() == row + 1,
            Self::optimal_path(points, row, col, n)[row] == col,
        decreases row + 1,
    {
        if row <= 0 {
            let path = seq![col];
            assert(path.len() == 1);
            assert(path[0] == col);
            assert forall|r: int| 0 <= r < 1 implies 0 <= #[trigger] path[r] < n by {};
        } else {
            Self::best_transfer_argmax_achieves(points, row, col, n - 1);
            let prev_col = Self::best_transfer_argmax(points, row, col, n - 1);
            Self::optimal_path_valid(points, row - 1, prev_col, n);
            let prev_path = Self::optimal_path(points, row - 1, prev_col, n);
            let full_path = prev_path.push(col);
            assert forall|r: int| 0 <= r < row + 1 implies 0 <= #[trigger] full_path[r] < n by {
                if r < row {
                    assert(full_path[r] == prev_path[r]);
                }
            };
        }
    }

    
    proof fn optimal_path_score(
        points: Seq<Vec<i32>>,
        row: int,
        col: int,
        n: int,
    )
        requires
            0 <= row < points.len() as int,
            0 <= col < n,
            n == points[0].len() as int,
            n >= 1,
            points.len() >= 1,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            Self::path_score(points, Self::optimal_path(points, row, col, n))
                == Self::dp_val(points, row, col),
        decreases row + 1,
    {
        let path = Self::optimal_path(points, row, col, n);
        if row <= 0 {
            assert(path == seq![col]);
            assert(Self::path_points_sum(points, path, 0)
                == Self::path_points_sum(points, path, -1int) + points[0][col] as int);
            assert(Self::path_points_sum(points, path, -1int) == 0);
            assert(Self::path_transition_cost(path, 0) == 0);
        } else {
            Self::best_transfer_argmax_achieves(points, row, col, n - 1);
            let prev_col = Self::best_transfer_argmax(points, row, col, n - 1);
            Self::optimal_path_valid(points, row - 1, prev_col, n);
            Self::optimal_path_score(points, row - 1, prev_col, n);
            Self::optimal_path_valid(points, row, col, n);

            let prev_path = Self::optimal_path(points, row - 1, prev_col, n);
            Self::path_score_decompose(points, path, row);

            assert forall|i: int| 0 <= i <= row - 1 implies path[i] == prev_path[i] by {};
            Self::path_points_sum_agree(points, path, prev_path, row - 1);
            Self::path_transition_cost_agree(path, prev_path, row - 1);

            assert(path[row] == col);
            assert(path[row - 1] == prev_col);
        }
    }

    
    proof fn dp_val_achievable(
        points: Seq<Vec<i32>>,
        row: int,
        col: int,
        n: int,
    )
        requires
            0 <= row < points.len() as int,
            0 <= col < n,
            n == points[0].len() as int,
            n >= 1,
            points.len() >= 1,
            points.len() * points[0].len() <= 100_000,
            forall|r: int|
                0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
            forall|r: int, c: int|
                0 <= r < points.len() && 0 <= c < points[0].len()
                    ==> 0 <= #[trigger] points[r][c] <= 100_000,
        ensures
            exists|path: Seq<int>|
                Self::valid_path(path, row + 1, n)
                && path[row] == col
                && Self::path_score(points, path) == Self::dp_val(points, row, col),
    {
        Self::optimal_path_valid(points, row, col, n);
        Self::optimal_path_score(points, row, col, n);
        let path = Self::optimal_path(points, row, col, n);
        assert(Self::valid_path(path, row + 1, n));
        assert(path[row] == col);
        assert(Self::path_score(points, path) == Self::dp_val(points, row, col));
    }
}

}
