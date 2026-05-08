impl Solution {
    pub fn num_moves_stones(a: i32, b: i32, c: i32) -> Vec<i32> {
        let mut x = a;
        let mut y = b;
        let mut z = c;
        if x > y {
            let tmp = x;
            x = y;
            y = tmp;
        }
        if x > z {
            let tmp = x;
            x = z;
            z = tmp;
        }
        if y > z {
            let tmp = y;
            y = z;
            z = tmp;
        }
        let min_moves;
        if y - x == 1 && z - y == 1 {
            min_moves = 0;
        } else if y - x <= 2 || z - y <= 2 {
            min_moves = 1;
        } else {
            min_moves = 2;
        }
        let max_moves = z - x - 2;
        let mut result = Vec::new();
        result.push(min_moves);
        result.push(max_moves);
        result
    }
}
