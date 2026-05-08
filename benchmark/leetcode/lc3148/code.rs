impl Solution {
    fn spec_max_exec(a: i32, b: i32) -> i32 {
        if a >= b {
            a
        } else {
            b
        }
    }

    fn best_starts_for_target_exec(
        grid: &Vec<Vec<i32>>,
        target: usize,
        start: usize,
    ) -> i32 {
        let n = grid[0].len();
        let tr = target / n;
        let tc = target % n;
        let limit = (tr + 1) * (tc + 1);
        if start >= limit {
            -100000
        } else {
            let sr = start / (tc + 1);
            let sc = start % (tc + 1);
            let rest = Self::best_starts_for_target_exec(grid, target, start + 1);
            if sr == tr && sc == tc {
                rest
            } else {
                let score = grid[tr][tc] - grid[sr][sc];
                Self::spec_max_exec(score, rest)
            }
        }
    }

    fn best_targets_from_exec(grid: &Vec<Vec<i32>>, target: usize) -> i32 {
        let total = grid.len() * grid[0].len();
        if target >= total {
            -100000
        } else {
            let here = Self::best_starts_for_target_exec(grid, target, 0);
            let rest = Self::best_targets_from_exec(grid, target + 1);
            Self::spec_max_exec(here, rest)
        }
    }

    pub fn max_score(grid: Vec<Vec<i32>>) -> i32 {
        Self::best_targets_from_exec(&grid, 0)
    }
}
