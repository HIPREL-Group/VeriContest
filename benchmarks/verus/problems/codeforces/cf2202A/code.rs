impl Solution {
    pub fn parkour_reachable(x: i64, y: i64) -> bool {
        let diff = x - 2 * y;
        if diff % 3 != 0 {
            return false;
        }
        let m = diff / 3;
        if m < 0 {
            return false;
        }
        let need = if y >= 0 { 0i64 } else { -y };
        need <= m / 2
    }
}
