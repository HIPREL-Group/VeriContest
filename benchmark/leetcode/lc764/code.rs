fn set_cell(grid: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32)
{
    let mut current_row = grid[row].clone();
    current_row[col] = value;
    grid[row] = current_row;
}

impl Solution {
    pub fn order_of_largest_plus_sign(n: i32, mines: Vec<Vec<i32>>) -> i32
    {
        let nu = n as usize;

        let mut grid: Vec<Vec<i32>> = Vec::new();
        let mut row_idx = 0usize;
        while row_idx < nu
        {
            let mut row: Vec<i32> = Vec::new();
            let mut col_idx = 0usize;
            while col_idx < nu
            {
                row.push(n);
                col_idx += 1;
            }
            grid.push(row);
            row_idx += 1;
        }

        let mut idx = 0usize;
        while idx < mines.len()
        {
            let mine_ref = &mines[idx];
            let r = mine_ref[0] as usize;
            let c = mine_ref[1] as usize;
            set_cell(&mut grid, r, c, 0);
            idx += 1;
        }

        let mut i = 0usize;
        while i < nu
        {
            let mut left = 0i32;
            let mut j = 0usize;
            while j < nu
            {
                if grid[i][j] != 0 {
                    left = left + 1;
                } else {
                    left = 0;
                }
                if left < grid[i][j] {
                    set_cell(&mut grid, i, j, left);
                }
                j += 1;
            }
            let mut right = 0i32;
            let mut j = nu;
            while j > 0
            {
                j -= 1;
                if grid[i][j] != 0 {
                    right = right + 1;
                } else {
                    right = 0;
                }
                if right < grid[i][j] {
                    set_cell(&mut grid, i, j, right);
                }
            }
            i += 1;
        }

        let mut i = 0usize;
        while i < nu
        {
            let mut up = 0i32;
            let mut j = 0usize;
            while j < nu
            {
                if grid[j][i] != 0 {
                    up = up + 1;
                } else {
                    up = 0;
                }
                if up < grid[j][i] {
                    set_cell(&mut grid, j, i, up);
                }
                j += 1;
            }
            let mut down = 0i32;
            let mut j = nu;
            while j > 0
            {
                j -= 1;
                if grid[j][i] != 0 {
                    down = down + 1;
                } else {
                    down = 0;
                }
                if down < grid[j][i] {
                    set_cell(&mut grid, j, i, down);
                }
            }
            i += 1;
        }

        let mut res = 0i32;
        let mut i = 0usize;
        while i < nu
        {
            let mut j = 0usize;
            while j < nu
            {
                if grid[i][j] > res {
                    res = grid[i][j];
                }
                j += 1;
            }
            i += 1;
        }

        res
    }
}
