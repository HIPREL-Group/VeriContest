impl Solution {
    pub fn num_moves_stones_ii(stones: Vec<i32>) -> Vec<i32> {
        let mut stones = stones;
        let n = stones.len();

        let mut si: usize = 1;
        while si < n {
            let mut sj: usize = si;
            while sj > 0 && stones[sj - 1] > stones[sj] {
                let tmp = stones[sj];
                stones[sj] = stones[sj - 1];
                stones[sj - 1] = tmp;
                sj = sj - 1;
            }
            si = si + 1;
        }

        let max_left = stones[n - 1] - stones[1] - n as i32 + 2;
        let max_right = stones[n - 2] - stones[0] - n as i32 + 2;
        let max_moves = if max_left >= max_right { max_left } else { max_right };

        let mut min_moves: i32 = n as i32;
        let mut i: usize = 0;
        let mut j: usize = 0;

        while j < n {
            while stones[j] - stones[i] >= n as i32 {
                i = i + 1;
            }
            let count = (j - i + 1) as i32;
            if count == n as i32 - 1 && stones[j] - stones[i] == n as i32 - 2 {
                if 2 < min_moves {
                    min_moves = 2;
                }
            } else {
                let cost = n as i32 - count;
                if cost < min_moves {
                    min_moves = cost;
                }
            }
            j = j + 1;
        }

        let mut result = Vec::new();
        result.push(min_moves);
        result.push(max_moves);
        result
    }
}
