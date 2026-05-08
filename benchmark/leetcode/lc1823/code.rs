impl Solution {
    pub fn find_the_winner(n: i32, k: i32) -> i32 {
        let mut winner = 0;
        let mut i = 2;
        while i <= n {
            winner = (winner + k) % i;
            i += 1;
        }
        winner + 1
    }
}
