impl Solution {
    pub fn is_winner(player1: Vec<i32>, player2: Vec<i32>) -> i32 {
        let mut s1: i128 = 0;
        let mut i: usize = 0;
        while i < player1.len() {
            if (i >= 1 && player1[i - 1] == 10) || (i >= 2 && player1[i - 2] == 10) {
                s1 = s1 + 2 * player1[i] as i128;
            } else {
                s1 = s1 + player1[i] as i128;
            }
            i = i + 1;
        }

        let mut s2: i128 = 0;
        let mut j: usize = 0;
        while j < player2.len() {
            if (j >= 1 && player2[j - 1] == 10) || (j >= 2 && player2[j - 2] == 10) {
                s2 = s2 + 2 * player2[j] as i128;
            } else {
                s2 = s2 + player2[j] as i128;
            }
            j = j + 1;
        }

        if s1 > s2 {
            1
        } else if s2 > s1 {
            2
        } else {
            0
        }
    }
}
