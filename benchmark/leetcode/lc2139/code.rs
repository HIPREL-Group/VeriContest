impl Solution {
    pub fn min_moves(target: i32, max_doubles: i32) -> i32 {
        let mut t = target;
        let mut k = max_doubles;
        let mut moves = 0;
        while t > 1 && k > 0 {
            if t % 2 == 0 {
                t = t / 2;
                k = k - 1;
            } else {
                t = t - 1;
            }
            moves = moves + 1;
        }
        moves + (t - 1)
    }
}
