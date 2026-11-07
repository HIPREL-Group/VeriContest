impl Solution {
    pub fn max_score(grid: Vec<Vec<i32>>) -> i32 {
        let rows: usize = grid.len();
        let cols: usize = grid[0].len();

        let mut minv: Vec<Vec<i32>> = Vec::new();
        let mut ans: i32 = -100000;

        let mut r: usize = 0;
        while r < rows {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols {
                let gv: i32 = grid[r][c];
                let mval: i32;
                if r == 0 && c == 0 {
                    mval = gv;
                } else if r == 0 {
                    let left = row[c - 1];
                    mval = if gv <= left { gv } else { left };
                } else if c == 0 {
                    let up = minv[r - 1][0];
                    mval = if gv <= up { gv } else { up };
                } else {
                    let up = minv[r - 1][c];
                    let left = row[c - 1];
                    let m1 = if gv <= up { gv } else { up };
                    mval = if m1 <= left { m1 } else { left };
                }
                row.push(mval);

                let excl: i32;
                if r == 0 && c == 0 {
                    excl = 100001;
                } else if r == 0 {
                    excl = row[c - 1];
                } else if c == 0 {
                    excl = minv[r - 1][0];
                } else {
                    let up2 = minv[r - 1][c];
                    let left2 = row[c - 1];
                    excl = if up2 <= left2 { up2 } else { left2 };
                }

                let best: i32;
                if r == 0 && c == 0 {
                    best = -100000;
                } else {
                    best = gv - excl;
                }

                if best > ans {
                    ans = best;
                }
                c += 1;
            }
            minv.push(row);
            r += 1;
        }

        ans
    }
}
