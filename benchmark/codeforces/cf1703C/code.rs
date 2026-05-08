impl Solution {
    pub fn recover_digit(final_d: i32, move_deltas: Vec<i32>) -> i32 {
        let mut x = final_d;
        let mut idx = move_deltas.len();
        while idx > 0 {
            idx = idx - 1;
            let d = move_deltas[idx];
            if d == 1 {
                x = (x - 1 + 10) % 10;
            } else {
                x = (x + 1) % 10;
            }
        }
        x
    }
}
