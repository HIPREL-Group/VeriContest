impl Solution {
    fn set_cell(board: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32) {
        let mut current_row = board[row].clone();
        current_row[col] = value;
        board[row] = current_row;
    }

    fn live_neighbor(board: &Vec<Vec<i32>>, r: i32, c: i32) -> i32 {
        let rows = board.len() as i32;
        let cols = board[0].len() as i32;
        if 0 <= r && r < rows && 0 <= c && c < cols {
            let ru = r as usize;
            let cu = c as usize;
            if board[ru][cu] == 1 {
                1
            } else {
                0
            }
        } else {
            0
        }
    }

    fn count_live_neighbors(board: &Vec<Vec<i32>>, row: usize, col: usize) -> i32 {
        let a = Self::live_neighbor(board, row as i32 - 1, col as i32 - 1);
        let b = Self::live_neighbor(board, row as i32 - 1, col as i32);
        let c = Self::live_neighbor(board, row as i32 - 1, col as i32 + 1);
        let d = Self::live_neighbor(board, row as i32, col as i32 - 1);
        let e = Self::live_neighbor(board, row as i32, col as i32 + 1);
        let f = Self::live_neighbor(board, row as i32 + 1, col as i32 - 1);
        let g = Self::live_neighbor(board, row as i32 + 1, col as i32);
        let h = Self::live_neighbor(board, row as i32 + 1, col as i32 + 1);
        let total = a + b + c + d + e + f + g + h;
        total
    }

    pub fn game_of_life(board: &mut Vec<Vec<i32>>) {
        let rows = board.len();
        let cols = board[0].len();
        let mut orig: Vec<Vec<i32>> = Vec::new();
        let mut build_row = 0usize;
        while build_row < rows {
            let mut copied_row: Vec<i32> = Vec::new();
            let mut build_col = 0usize;
            while build_col < cols {
                copied_row.push(board[build_row][build_col]);
                build_col = build_col + 1;
            }
            orig.push(copied_row);
            build_row = build_row + 1;
        }
        let mut row = 0usize;
        while row < rows {
            let mut col = 0usize;
            while col < cols {
                let live = Self::count_live_neighbors(&orig, row, col);
                let mut new_val = 0i32;
                if orig[row][col] == 1 {
                    if live == 2 || live == 3 {
                        new_val = 1;
                    }
                } else {
                    if live == 3 {
                        new_val = 1;
                    }
                }
                Self::set_cell(board, row, col, new_val);
                col = col + 1;
            }
            row = row + 1;
        }
    }
}
