impl Solution {
    fn is_magic_square(grid: &Vec<Vec<i32>>, r: usize, c: usize) -> bool {
        let a = grid[r][c];
        let b = grid[r][c + 1];
        let c1 = grid[r][c + 2];
        let d = grid[r + 1][c];
        let e = grid[r + 1][c + 1];
        let f = grid[r + 1][c + 2];
        let g = grid[r + 2][c];
        let h = grid[r + 2][c + 1];
        let i = grid[r + 2][c + 2];

        1 <= a
            && a <= 9
            && 1 <= b
            && b <= 9
            && 1 <= c1
            && c1 <= 9
            && 1 <= d
            && d <= 9
            && 1 <= e
            && e <= 9
            && 1 <= f
            && f <= 9
            && 1 <= g
            && g <= 9
            && 1 <= h
            && h <= 9
            && 1 <= i
            && i <= 9
            && a != b
            && a != c1
            && a != d
            && a != e
            && a != f
            && a != g
            && a != h
            && a != i
            && b != c1
            && b != d
            && b != e
            && b != f
            && b != g
            && b != h
            && b != i
            && c1 != d
            && c1 != e
            && c1 != f
            && c1 != g
            && c1 != h
            && c1 != i
            && d != e
            && d != f
            && d != g
            && d != h
            && d != i
            && e != f
            && e != g
            && e != h
            && e != i
            && f != g
            && f != h
            && f != i
            && g != h
            && g != i
            && h != i
            && a + b + c1 == 15
            && d + e + f == 15
            && g + h + i == 15
            && a + d + g == 15
            && b + e + h == 15
            && c1 + f + i == 15
            && a + e + i == 15
            && c1 + e + g == 15
    }

    pub fn num_magic_squares_inside(grid: Vec<Vec<i32>>) -> i32 {
        let rows = grid.len();
        let cols = grid[0].len();
        let row_limit = if rows >= 3 { rows - 2 } else { 0 };
        let col_limit = if cols >= 3 { cols - 2 } else { 0 };
        let mut result: i32 = 0;
        let mut r: usize = 0;
        while r < row_limit {
            let mut c: usize = 0;
            while c < col_limit {
                let ok = Self::is_magic_square(&grid, r, c);
                if ok {
                    result = result + 1;
                }
                c = c + 1;
            }
            r = r + 1;
        }
        result
    }
}
