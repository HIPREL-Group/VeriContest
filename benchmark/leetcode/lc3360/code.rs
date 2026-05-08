impl Solution {
    pub fn can_alice_win(n: i32) -> bool {
        let mut stones = n;
        let mut take = 10;
        let mut alice_turn = true;
        while take > 0 && stones >= take {
            stones -= take;
            take -= 1;
            alice_turn = !alice_turn;
        }
        !alice_turn
    }
}
