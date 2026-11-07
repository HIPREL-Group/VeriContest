impl Solution {
    pub fn min_steps_to_target(r: i128, x: i128, y: i128, x2: i128, y2: i128) -> i128 {
        let dx = x2 - x;
        let dy = y2 - y;
        let dist_sq = dx * dx + dy * dy;
        let two_r = 2 * r;
        let jump_sq_val = two_r * two_r;
        let mut ans = 0i128;
        while ans < 200000 && jump_sq_val * ans * ans < dist_sq {
            ans += 1;
        }
        ans
    }
}
