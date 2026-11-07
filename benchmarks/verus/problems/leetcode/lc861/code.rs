impl Solution {
    pub fn matrix_score(grid: Vec<Vec<i32>>) -> i32 {
        let rows = grid.len();
        let cols = grid[0].len();
        let mut result: i32 = 0;
        let mut place: i32 = 1;
        let mut j: usize = cols;
        while j > 0 {
            let col = j - 1;
            let mut ones: i32 = 0;
            let mut i: usize = 0;
            while i < rows {
                let one = grid[i][col] == grid[i][0];
                if one {
                    ones = ones + 1;
                }
                i = i + 1;
            }
            let zeros = rows as i32 - ones;
            let best = if ones >= zeros { ones } else { zeros };
            result = result + best * place;
            place = place * 2;
            j = j - 1;
        }
        result
    }
}
