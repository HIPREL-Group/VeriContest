impl Solution {
    pub fn get_max_grid_happiness(m: i32, n: i32, introverts_count: i32, extroverts_count: i32) -> i32 {
        let mut pow3nm1: i32 = 1;
        let mut k: i32 = 1;
        while k < n {
            pow3nm1 = pow3nm1 * 3;
            k = k + 1;
        }
        Solution::solve(m, n, 0, introverts_count, extroverts_count, 0, pow3nm1)
    }

    fn solve(m: i32, n: i32, pos: i32, ic: i32, ec: i32, profile: i32, pow3nm1: i32) -> i32 {
        if pos >= m * n {
            return 0;
        }
        let row = pos / n;
        let col = pos % n;
        let up_type = profile % 3;
        let left_type = (profile / pow3nm1) % 3;
        let shifted = profile / 3;
        let val_empty = Solution::solve(m, n, pos + 1, ic, ec, shifted, pow3nm1);
        let mut best = val_empty;
        if ic > 0 {
            let base: i32 = 120;
            let adj_up: i32 = if row > 0 {
                if up_type == 0 { 0 } else if up_type == 1 { -60 } else { -10 }
            } else { 0 };
            let adj_left: i32 = if col > 0 {
                if left_type == 0 { 0 } else if left_type == 1 { -60 } else { -10 }
            } else { 0 };
            let d = base + adj_up + adj_left;
            let next_pr = shifted + pow3nm1;
            let val_intro = d + Solution::solve(m, n, pos + 1, ic - 1, ec, next_pr, pow3nm1);
            if val_intro > best {
                best = val_intro;
            }
        }
        if ec > 0 {
            let base: i32 = 40;
            let adj_up: i32 = if row > 0 {
                if up_type == 0 { 0 } else if up_type == 1 { -10 } else { 40 }
            } else { 0 };
            let adj_left: i32 = if col > 0 {
                if left_type == 0 { 0 } else if left_type == 1 { -10 } else { 40 }
            } else { 0 };
            let d = base + adj_up + adj_left;
            let next_pr = shifted + 2 * pow3nm1;
            let val_extro = d + Solution::solve(m, n, pos + 1, ic, ec - 1, next_pr, pow3nm1);
            if val_extro > best {
                best = val_extro;
            }
        }
        best
    }
}
