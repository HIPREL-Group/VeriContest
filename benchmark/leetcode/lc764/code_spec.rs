use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_mine(mines: Seq<Vec<i32>>, r: int, c: int) -> bool {
    exists|i: int| 0 <= i < mines.len() && mines[i].len() == 2
        && mines[i][0] as int == r
        && mines[i][1] as int == c
}

pub open spec fn grid_val(n: int, mines: Seq<Vec<i32>>, r: int, c: int) -> int {
    if 0 <= r < n && 0 <= c < n && is_mine(mines, r, c) {
        0
    } else {
        1
    }
}

pub open spec fn has_plus_of_order(n: int, mines: Seq<Vec<i32>>, r: int, c: int, k: int) -> bool {
    grid_val(n, mines, r, c) == 1
        && forall|i: int| 1 <= i <= k - 1 ==> (
            c - i >= 0
            && c + i < n
            && r - i >= 0
            && r + i < n
            && #[trigger] grid_val(n, mines, r, c - i) == 1
            && grid_val(n, mines, r, c + i) == 1
            && grid_val(n, mines, r - i, c) == 1
            && grid_val(n, mines, r + i, c) == 1
        )
}

fn set_cell(grid: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32)
    requires
        row < old(grid)@.len(),
        col < old(grid)@[row as int].len(),
    ensures
        grid@.len() == old(grid)@.len(),
        forall|r: int| 0 <= r < grid@.len() ==> #[trigger] grid@[r].len() == old(grid)@[r].len(),
        forall|r: int, c: int|
            0 <= r < grid@.len() && 0 <= c < grid@[r].len() ==> #[trigger] grid@[r][c]
                == if r == row as int && c == col as int { value } else { old(grid)@[r][c] },
{
    let mut current_row = grid[row].clone();
    current_row[col] = value;
    grid[row] = current_row;
}

impl Solution {
    #[verifier::loop_isolation(false)]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn order_of_largest_plus_sign(n: i32, mines: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= n <= 500,
            1 <= mines.len() <= 5000,
            forall|i: int| 0 <= i < mines.len() ==> #[trigger] mines[i].len() == 2,
            forall|i: int| 0 <= i < mines.len() ==> 0 <= #[trigger] mines[i][0] < n && 0 <= mines[i][1] < n,
            forall|i: int, j: int|
                0 <= i < j < mines.len()
                ==> (mines[i][0] != mines[j][0] || mines[i][1] != mines[j][1]),
        ensures
            result >= 0 && result <= n,
            result > 0 ==> exists|r: int, c: int|
                0 <= r < n as int
                && 0 <= c < n as int
                && has_plus_of_order(n as int, mines@, r, c, result as int),
            forall|k: int, r: int, c: int|
                (result as int) < k && k <= (n as int) && 0 <= r < (n as int) && 0 <= c < (n as int)
                ==> !has_plus_of_order(n as int, mines@, r, c, k),
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

}
