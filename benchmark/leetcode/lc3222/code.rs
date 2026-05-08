impl Solution {
    pub fn winning_player(x: i32, y: i32) -> String {
        let turns = if x <= y / 4 { x } else { y / 4 };
        if turns % 2 == 1 {
            "Alice".to_string()
        } else {
            "Bob".to_string()
        }
    }
}
