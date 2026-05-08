impl Solution {
    pub fn min_moves_to_capture_the_queen(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32) -> i32 {
        let rook_row_attack = a == e && !(c == a && ((b < d && d < f) || (f < d && d < b)));
        let rook_col_attack = b == f && !(d == b && ((a < c && c < e) || (e < c && c < a)));
        let rook_attack = rook_row_attack || rook_col_attack;

        let bishop_diag_sum = c + d == e + f;
        let bishop_diag_diff = c - d == e - f;
        let bishop_attack = if bishop_diag_sum {
            !(a + b == c + d && ((c < a && a < e) || (e < a && a < c)))
        } else if bishop_diag_diff {
            !(a - b == c - d && ((c < a && a < e) || (e < a && a < c)))
        } else {
            false
        };

        if rook_attack || bishop_attack {
            1
        } else {
            2
        }
    }
}
